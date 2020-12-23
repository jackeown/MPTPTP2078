%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1304+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:05 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  95 expanded)
%              Number of clauses        :   25 (  37 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 403 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( v1_tops_2(X2,X1)
               => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tops_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(dt_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k7_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(redefinition_k7_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k7_subset_1(X1,X2,X3) = k4_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( v1_tops_2(X2,X1)
                 => v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_tops_2])).

fof(c_0_6,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_tops_2(X6,X5)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X7,X6)
        | v3_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( m1_subset_1(esk1_2(X5,X6),k1_zfmisc_1(u1_struct_0(X5)))
        | v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) )
      & ( ~ v3_pre_topc(esk1_2(X5,X6),X5)
        | v1_tops_2(X6,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X5))))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_7,plain,(
    ! [X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X18))
      | m1_subset_1(k7_subset_1(X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_subset_1])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))
    & v1_tops_2(esk4_0,esk3_0)
    & ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | k7_subset_1(X21,X22,X23) = k4_xboole_0(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_subset_1])])).

cnf(c_0_10,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(k7_subset_1(X2,X1,X3),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_tops_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( k7_subset_1(X2,X1,X3) = k4_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)
    | ~ v3_pre_topc(esk1_2(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3)),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_20,plain,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3),X1)
    | m1_subset_1(esk1_2(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X1)),X2,X3)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

fof(c_0_21,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( r2_hidden(X12,X9)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(X13,X9)
        | r2_hidden(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k4_xboole_0(X9,X10) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | ~ r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X15)
        | X16 = k4_xboole_0(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X14)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) )
      & ( ~ r2_hidden(esk2_3(X14,X15,X16),X15)
        | r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k4_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),X1,X2),esk3_0)
    | ~ r2_hidden(esk1_2(esk3_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),X1,X2)),esk4_0)
    | ~ m1_subset_1(esk1_2(esk3_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),X1,X2)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_15])])).

cnf(c_0_25,negated_conjecture,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,X1),esk3_0)
    | m1_subset_1(esk1_2(esk3_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,X1)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_15])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,k4_xboole_0(X2,X3)),k4_xboole_0(X2,X3))
    | v1_tops_2(k4_xboole_0(X2,X3),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,X1),esk3_0)
    | ~ r2_hidden(esk1_2(esk3_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,X1)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(esk3_0)),esk4_0,esk5_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,k4_xboole_0(esk4_0,X1)),k4_xboole_0(esk4_0,X1))
    | v1_tops_2(k4_xboole_0(esk4_0,X1),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_13]),c_0_15])])).

cnf(c_0_32,negated_conjecture,
    ( v1_tops_2(k4_xboole_0(esk4_0,X1),esk3_0)
    | ~ r2_hidden(esk1_2(esk3_0,k4_xboole_0(esk4_0,X1)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_17]),c_0_13])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_tops_2(k4_xboole_0(esk4_0,esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_13])])).

cnf(c_0_34,negated_conjecture,
    ( v1_tops_2(k4_xboole_0(esk4_0,X1),esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])]),
    [proof]).

%------------------------------------------------------------------------------
