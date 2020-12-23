%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (1083 expanded)
%              Number of clauses        :   34 ( 360 expanded)
%              Number of leaves         :    5 ( 260 expanded)
%              Depth                    :   12
%              Number of atoms          :  319 (10555 expanded)
%              Number of equality atoms :   48 (2137 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   62 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d15_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( X2 != k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> ? [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                        & r2_hidden(X4,X2)
                        & X3 = k3_orders_2(X1,X2,X4) ) ) )
                & ( X2 = k1_xboole_0
                 => ( m1_orders_2(X3,X1,X2)
                  <=> X3 = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(dt_m1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m1_orders_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(t68_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k1_xboole_0
                & m1_orders_2(X2,X1,X2) )
            & ~ ( ~ m1_orders_2(X2,X1,X2)
                & X2 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

fof(t57_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(irreflexivity_r2_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ~ r2_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X12] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))
        | ~ m1_orders_2(X10,X8,X9)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | ~ m1_orders_2(X10,X8,X9)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( X10 = k3_orders_2(X8,X9,esk1_3(X8,X9,X10))
        | ~ m1_orders_2(X10,X8,X9)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X8))
        | ~ r2_hidden(X12,X9)
        | X10 != k3_orders_2(X8,X9,X12)
        | m1_orders_2(X10,X8,X9)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_orders_2(X10,X8,X9)
        | X10 = k1_xboole_0
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( X10 != k1_xboole_0
        | m1_orders_2(X10,X8,X9)
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).

fof(c_0_6,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v3_orders_2(X13)
      | ~ v4_orders_2(X13)
      | ~ v5_orders_2(X13)
      | ~ l1_orders_2(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ m1_orders_2(X15,X13,X14)
      | m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( ~ ( X2 != k1_xboole_0
                  & m1_orders_2(X2,X1,X2) )
              & ~ ( ~ m1_orders_2(X2,X1,X2)
                  & X2 = k1_xboole_0 ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t68_orders_2])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ m1_orders_2(esk3_0,esk2_0,esk3_0)
      | esk3_0 != k1_xboole_0 )
    & ( esk3_0 = k1_xboole_0
      | esk3_0 != k1_xboole_0 )
    & ( ~ m1_orders_2(esk3_0,esk2_0,esk3_0)
      | m1_orders_2(esk3_0,esk2_0,esk3_0) )
    & ( esk3_0 = k1_xboole_0
      | m1_orders_2(esk3_0,esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

cnf(c_0_11,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))
    | ~ m1_orders_2(X3,X2,X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_18,plain,(
    ! [X19,X20,X21,X22] :
      ( ( r2_orders_2(X19,X20,X21)
        | ~ r2_hidden(X20,k3_orders_2(X19,X22,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19) )
      & ( r2_hidden(X20,X22)
        | ~ r2_hidden(X20,k3_orders_2(X19,X22,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19) )
      & ( ~ r2_orders_2(X19,X20,X21)
        | ~ r2_hidden(X20,X22)
        | r2_hidden(X20,k3_orders_2(X19,X22,X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).

cnf(c_0_19,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_orders_2(esk3_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,plain,
    ( r2_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,k3_orders_2(X1,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( X1 = k3_orders_2(X2,X3,esk1_3(X2,X3,X1))
    | X3 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_25,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k3_orders_2(esk2_0,X2,esk1_3(esk2_0,esk3_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_26,plain,
    ( k3_orders_2(X1,X2,esk1_3(X1,X2,X3)) = X3
    | X2 = k1_xboole_0
    | v2_struct_0(X1)
    | ~ m1_orders_2(X3,X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_23,c_0_9])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | r2_hidden(esk1_3(X2,X1,X3),X1)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_24,c_0_9])).

fof(c_0_28,plain,(
    ! [X16,X17,X18] :
      ( ~ l1_orders_2(X16)
      | ~ m1_subset_1(X17,u1_struct_0(X16))
      | ~ m1_subset_1(X18,u1_struct_0(X16))
      | ~ r2_orders_2(X16,X17,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1)) = X1
    | esk3_0 = k1_xboole_0
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk3_0)
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_32,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) = esk3_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_orders_2(esk2_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_22]),c_0_13])])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_38,plain,
    ( m1_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( ~ m1_orders_2(esk3_0,esk2_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_41,plain,
    ( m1_orders_2(k1_xboole_0,X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ m1_orders_2(k1_xboole_0,esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_39]),c_0_39]),c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_43]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(d15_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((X2!=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X1))&r2_hidden(X4,X2))&X3=k3_orders_2(X1,X2,X4))))&(X2=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>X3=k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 0.20/0.38  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 0.20/0.38  fof(t68_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k1_xboole_0&m1_orders_2(X2,X1,X2)))&~((~(m1_orders_2(X2,X1,X2))&X2=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 0.20/0.38  fof(t57_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,k3_orders_2(X1,X4,X3))<=>(r2_orders_2(X1,X2,X3)&r2_hidden(X2,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 0.20/0.38  fof(irreflexivity_r2_orders_2, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>~(r2_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_orders_2)).
% 0.20/0.38  fof(c_0_5, plain, ![X8, X9, X10, X12]:(((((m1_subset_1(esk1_3(X8,X9,X10),u1_struct_0(X8))|~m1_orders_2(X10,X8,X9)|X9=k1_xboole_0|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))&(r2_hidden(esk1_3(X8,X9,X10),X9)|~m1_orders_2(X10,X8,X9)|X9=k1_xboole_0|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))&(X10=k3_orders_2(X8,X9,esk1_3(X8,X9,X10))|~m1_orders_2(X10,X8,X9)|X9=k1_xboole_0|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))&(~m1_subset_1(X12,u1_struct_0(X8))|~r2_hidden(X12,X9)|X10!=k3_orders_2(X8,X9,X12)|m1_orders_2(X10,X8,X9)|X9=k1_xboole_0|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))&((~m1_orders_2(X10,X8,X9)|X10=k1_xboole_0|X9!=k1_xboole_0|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))&(X10!=k1_xboole_0|m1_orders_2(X10,X8,X9)|X9!=k1_xboole_0|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).
% 0.20/0.38  fof(c_0_6, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v3_orders_2(X13)|~v4_orders_2(X13)|~v5_orders_2(X13)|~l1_orders_2(X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_orders_2(X15,X13,X14)|m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 0.20/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k1_xboole_0&m1_orders_2(X2,X1,X2)))&~((~(m1_orders_2(X2,X1,X2))&X2=k1_xboole_0)))))), inference(assume_negation,[status(cth)],[t68_orders_2])).
% 0.20/0.38  cnf(c_0_8, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_9, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  fof(c_0_10, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(((~m1_orders_2(esk3_0,esk2_0,esk3_0)|esk3_0!=k1_xboole_0)&(esk3_0=k1_xboole_0|esk3_0!=k1_xboole_0))&((~m1_orders_2(esk3_0,esk2_0,esk3_0)|m1_orders_2(esk3_0,esk2_0,esk3_0))&(esk3_0=k1_xboole_0|m1_orders_2(esk3_0,esk2_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 0.20/0.38  cnf(c_0_11, plain, (X1=k1_xboole_0|v2_struct_0(X2)|m1_subset_1(esk1_3(X2,X1,X3),u1_struct_0(X2))|~m1_orders_2(X3,X2,X1)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_8, c_0_9])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_14, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_18, plain, ![X19, X20, X21, X22]:(((r2_orders_2(X19,X20,X21)|~r2_hidden(X20,k3_orders_2(X19,X22,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)))&(r2_hidden(X20,X22)|~r2_hidden(X20,k3_orders_2(X19,X22,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19))))&(~r2_orders_2(X19,X20,X21)|~r2_hidden(X20,X22)|r2_hidden(X20,k3_orders_2(X19,X22,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X19)))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_orders_2])])])])])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk1_3(esk2_0,esk3_0,X1),u1_struct_0(esk2_0))|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (esk3_0=k1_xboole_0|m1_orders_2(esk3_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_21, plain, (r2_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r2_hidden(X2,k3_orders_2(X1,X4,X3))|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_23, plain, (X1=k3_orders_2(X2,X3,esk1_3(X2,X3,X1))|X3=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,k3_orders_2(esk2_0,X2,esk1_3(esk2_0,esk3_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.38  cnf(c_0_26, plain, (k3_orders_2(X1,X2,esk1_3(X1,X2,X3))=X3|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_23, c_0_9])).
% 0.20/0.38  cnf(c_0_27, plain, (X1=k1_xboole_0|v2_struct_0(X2)|r2_hidden(esk1_3(X2,X1,X3),X1)|~m1_orders_2(X3,X2,X1)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_24, c_0_9])).
% 0.20/0.38  fof(c_0_28, plain, ![X16, X17, X18]:(~l1_orders_2(X16)|~m1_subset_1(X17,u1_struct_0(X16))|~m1_subset_1(X18,u1_struct_0(X16))|~r2_orders_2(X16,X17,X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_25, c_0_22])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))=X1|esk3_0=k1_xboole_0|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_3(esk2_0,esk3_0,X1),esk3_0)|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.20/0.38  cnf(c_0_32, plain, (~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_orders_2(X1,X2,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))|~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)))), inference(spm,[status(thm)],[c_0_29, c_0_12])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))=esk3_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (esk3_0=k1_xboole_0|r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (esk3_0=k1_xboole_0|~r2_orders_2(esk2_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_22]), c_0_13])])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (esk3_0=k1_xboole_0|r2_orders_2(esk2_0,esk1_3(esk2_0,esk3_0,esk3_0),esk1_3(esk2_0,esk3_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.20/0.38  cnf(c_0_38, plain, (m1_orders_2(X1,X2,X3)|v2_struct_0(X2)|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_22])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (~m1_orders_2(esk3_0,esk2_0,esk3_0)|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_41, plain, (m1_orders_2(k1_xboole_0,X1,k1_xboole_0)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_12, c_0_39])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (~m1_orders_2(k1_xboole_0,esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_39]), c_0_39]), c_0_39])])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_43]), c_0_17]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 45
% 0.20/0.38  # Proof object clause steps            : 34
% 0.20/0.38  # Proof object formula steps           : 11
% 0.20/0.38  # Proof object conjectures             : 26
% 0.20/0.38  # Proof object clause conjectures      : 23
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 15
% 0.20/0.38  # Proof object initial formulas used   : 5
% 0.20/0.38  # Proof object generating inferences   : 13
% 0.20/0.38  # Proof object simplifying inferences  : 45
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 22
% 0.20/0.38  # Removed in clause preprocessing      : 2
% 0.20/0.38  # Initial clauses in saturation        : 20
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 66
% 0.20/0.38  # Other redundant clauses eliminated   : 4
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 21
% 0.20/0.38  # Generated clauses                    : 32
% 0.20/0.38  # ...of the previous two non-trivial   : 34
% 0.20/0.38  # Contextual simplify-reflections      : 8
% 0.20/0.38  # Paramodulations                      : 29
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 4
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
% 0.20/0.38  # Current number of processed clauses  : 20
% 0.20/0.38  #    Positive orientable unit clauses  : 6
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 12
% 0.20/0.38  # Current number of unprocessed clauses: 3
% 0.20/0.38  # ...number of literals in the above   : 6
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 43
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 557
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 94
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.20/0.38  # Unit Clause-clause subsumption calls : 1
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 3
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4028
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.036 s
% 0.20/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
