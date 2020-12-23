%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1123+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:45 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 408 expanded)
%              Number of clauses        :   47 ( 154 expanded)
%              Number of leaves         :    9 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  347 (4093 expanded)
%              Number of equality atoms :   28 ( 204 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   76 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ( ~ v2_struct_0(X1)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ~ ( v3_pre_topc(X4,X1)
                          & r2_hidden(X3,X4)
                          & r1_xboole_0(X2,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ( ~ v2_struct_0(X1)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & r2_hidden(X3,X4)
                            & r1_xboole_0(X2,X4) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_pre_topc])).

fof(c_0_10,negated_conjecture,(
    ! [X31] :
      ( l1_pre_topc(esk4_0)
      & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | v2_struct_0(esk4_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( v3_pre_topc(esk7_0,esk4_0)
        | v2_struct_0(esk4_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( r2_hidden(esk6_0,esk7_0)
        | v2_struct_0(esk4_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( r1_xboole_0(esk5_0,esk7_0)
        | v2_struct_0(esk4_0)
        | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( ~ v2_struct_0(esk4_0)
        | r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) )
      & ( ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ v3_pre_topc(X31,esk4_0)
        | ~ r2_hidden(esk6_0,X31)
        | ~ r1_xboole_0(esk5_0,X31)
        | r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_11,plain,(
    ! [X6,X7,X8,X9,X10,X14] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X10,X6)
        | ~ r2_hidden(X9,X10)
        | ~ r1_xboole_0(X7,X10)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_4(X6,X7,X8,X9),k1_zfmisc_1(u1_struct_0(X6)))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk1_4(X6,X7,X8,X9),X6)
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(X9,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(X7,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk3_3(X6,X7,X8),X6)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(X7,esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X14,X6)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X14)
        | ~ r1_xboole_0(X7,X14)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

cnf(c_0_12,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v3_pre_topc(X1,esk4_0)
    | ~ r2_hidden(esk6_0,X1)
    | ~ r1_xboole_0(esk5_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,esk1_4(X2,X1,X3,X4))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | X3 != k2_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(X1,X2)
    | X2 != k2_pre_topc(X3,esk5_0)
    | ~ v3_pre_topc(esk1_4(X3,esk5_0,X2,X1),esk4_0)
    | ~ r2_hidden(esk6_0,esk1_4(X3,esk5_0,X2,X1))
    | ~ r2_hidden(X1,u1_struct_0(X3))
    | ~ m1_subset_1(esk1_4(X3,esk5_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_15,plain,
    ( v3_pre_topc(esk1_4(X1,X2,X3,X4),X1)
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | m1_subset_1(k2_pre_topc(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(X1,X2)
    | X2 != k2_pre_topc(esk4_0,esk5_0)
    | ~ r2_hidden(esk6_0,esk1_4(esk4_0,esk5_0,X2,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk1_4(esk4_0,esk5_0,X2,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,esk1_4(X2,X3,X4,X1))
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | X4 != k2_pre_topc(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_21,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k2_pre_topc(esk4_0,esk5_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk1_4(esk4_0,esk5_0,X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_16]),c_0_17])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | X3 = k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v3_pre_topc(X3,X4)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X5,X3)
    | ~ r2_hidden(X1,u1_struct_0(X4))
    | X2 != k2_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k2_pre_topc(esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | r2_hidden(esk6_0,X1)
    | X1 != k2_pre_topc(esk4_0,esk5_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_16]),c_0_17])])).

cnf(c_0_31,plain,
    ( X1 = k2_pre_topc(X2,X3)
    | ~ v1_xboole_0(u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X18] :
      ( ~ v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_34,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_35,negated_conjecture,
    ( k2_pre_topc(esk4_0,X1) != k2_pre_topc(esk4_0,X2)
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X3,esk4_0)
    | ~ r2_hidden(X4,k2_pre_topc(esk4_0,X1))
    | ~ r2_hidden(X4,u1_struct_0(esk4_0))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_17])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 = k2_pre_topc(esk4_0,X1)
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_17])])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_40,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) != k2_pre_topc(esk4_0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_16])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_16])]),c_0_39])).

cnf(c_0_44,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) != k2_pre_topc(esk4_0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ v3_pre_topc(X2,esk4_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_29]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(esk7_0,esk4_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_17])])).

cnf(c_0_48,negated_conjecture,
    ( k2_pre_topc(esk4_0,esk5_0) != k2_pre_topc(esk4_0,X1)
    | ~ r1_xboole_0(X1,esk7_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,esk7_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk7_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,esk7_0)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_16])]),c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v2_struct_0(esk4_0)
    | ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_54,plain,(
    ! [X20,X21] :
      ( ~ m1_subset_1(X20,X21)
      | v1_xboole_0(X21)
      | r2_hidden(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k2_pre_topc(esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_47])).

fof(c_0_56,plain,(
    ! [X19] :
      ( v2_struct_0(X19)
      | ~ l1_struct_0(X19)
      | ~ v1_xboole_0(u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk6_0,u1_struct_0(esk4_0))
    | ~ m1_subset_1(k2_pre_topc(esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk6_0,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_16])])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_17])]),c_0_47]),
    [proof]).

%------------------------------------------------------------------------------
