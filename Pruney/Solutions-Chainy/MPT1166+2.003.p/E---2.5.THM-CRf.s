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
% DateTime   : Thu Dec  3 11:10:00 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 377 expanded)
%              Number of clauses        :   32 ( 120 expanded)
%              Number of leaves         :    6 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  240 (2855 expanded)
%              Number of equality atoms :   31 ( 293 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   62 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_orders_2,conjecture,(
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
             => ~ ( X2 != k1_xboole_0
                  & m1_orders_2(X2,X1,X3)
                  & m1_orders_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(t67_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_orders_2(X3,X1,X2)
             => r1_tarski(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(t60_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_tarski(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

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

fof(t62_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ r2_hidden(X2,k3_orders_2(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( X2 != k1_xboole_0
                    & m1_orders_2(X2,X1,X3)
                    & m1_orders_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_orders_2])).

fof(c_0_7,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_orders_2(X19,X17,X18)
      | r1_tarski(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 != k1_xboole_0
    & m1_orders_2(esk3_0,esk2_0,esk4_0)
    & m1_orders_2(esk4_0,esk2_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X7,X8] :
      ( ~ r1_tarski(X7,X8)
      | ~ r2_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ m1_orders_2(X1,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_orders_2(esk3_0,esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ m1_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_16]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X13] :
      ( ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | ~ m1_orders_2(X11,X9,X10)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | ~ m1_orders_2(X11,X9,X10)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( X11 = k3_orders_2(X9,X10,esk1_3(X9,X10,X11))
        | ~ m1_orders_2(X11,X9,X10)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X9))
        | ~ r2_hidden(X13,X10)
        | X11 != k3_orders_2(X9,X10,X13)
        | m1_orders_2(X11,X9,X10)
        | X10 = k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_orders_2(X11,X9,X10)
        | X11 = k1_xboole_0
        | X10 != k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( X11 != k1_xboole_0
        | m1_orders_2(X11,X9,X10)
        | X10 != k1_xboole_0
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).

cnf(c_0_26,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_31,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v3_orders_2(X14)
      | ~ v4_orders_2(X14)
      | ~ v5_orders_2(X14)
      | ~ l1_orders_2(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ r2_hidden(X15,k3_orders_2(X14,X16,X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_orders_2])])])])).

cnf(c_0_32,negated_conjecture,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk1_3(esk2_0,X1,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_orders_2(esk3_0,esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( m1_orders_2(esk3_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_16])]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1)) = X1
    | ~ m1_orders_2(X1,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_34]),c_0_15])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_33]),c_0_16])])).

cnf(c_0_42,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(esk2_0,X1,esk3_0),X1)
    | ~ m1_orders_2(esk3_0,esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_16]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_16]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_16])]),c_0_34]),c_0_43]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:20:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.12/0.37  # and selection function SelectNewComplexAHP.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t69_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 0.12/0.37  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.12/0.37  fof(t60_xboole_1, axiom, ![X1, X2]:~((r1_tarski(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 0.12/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.12/0.37  fof(d15_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((X2!=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X1))&r2_hidden(X4,X2))&X3=k3_orders_2(X1,X2,X4))))&(X2=k1_xboole_0=>(m1_orders_2(X3,X1,X2)<=>X3=k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 0.12/0.37  fof(t62_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(r2_hidden(X2,k3_orders_2(X1,X3,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_orders_2)).
% 0.12/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2))))))), inference(assume_negation,[status(cth)],[t69_orders_2])).
% 0.12/0.37  fof(c_0_7, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~m1_orders_2(X19,X17,X18)|r1_tarski(X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.12/0.37  fof(c_0_8, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((esk3_0!=k1_xboole_0&m1_orders_2(esk3_0,esk2_0,esk4_0))&m1_orders_2(esk4_0,esk2_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.12/0.37  cnf(c_0_9, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_17, plain, ![X7, X8]:(~r1_tarski(X7,X8)|~r2_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_xboole_1])])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (r1_tarski(X1,esk4_0)|~m1_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (m1_orders_2(esk3_0,esk2_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_20, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(X1,esk3_0)|~m1_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_16]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_23, plain, (~r1_tarski(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  fof(c_0_25, plain, ![X9, X10, X11, X13]:(((((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|~m1_orders_2(X11,X9,X10)|X10=k1_xboole_0|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&(r2_hidden(esk1_3(X9,X10,X11),X10)|~m1_orders_2(X11,X9,X10)|X10=k1_xboole_0|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))&(X11=k3_orders_2(X9,X10,esk1_3(X9,X10,X11))|~m1_orders_2(X11,X9,X10)|X10=k1_xboole_0|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))&(~m1_subset_1(X13,u1_struct_0(X9))|~r2_hidden(X13,X10)|X11!=k3_orders_2(X9,X10,X13)|m1_orders_2(X11,X9,X10)|X10=k1_xboole_0|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))&((~m1_orders_2(X11,X9,X10)|X11=k1_xboole_0|X10!=k1_xboole_0|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&(X11!=k1_xboole_0|m1_orders_2(X11,X9,X10)|X10!=k1_xboole_0|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d15_orders_2])])])])])])).
% 0.12/0.37  cnf(c_0_26, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (~r2_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_29, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (esk4_0=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.12/0.37  fof(c_0_31, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)|(~m1_subset_1(X15,u1_struct_0(X14))|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X15,k3_orders_2(X14,X16,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t62_orders_2])])])])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (X1=k1_xboole_0|m1_subset_1(esk1_3(esk2_0,X1,esk3_0),u1_struct_0(esk2_0))|~m1_orders_2(esk3_0,esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (m1_orders_2(esk3_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_19, c_0_30])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_35, plain, (X1=k3_orders_2(X2,X3,esk1_3(X2,X3,X1))|X3=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,k3_orders_2(X1,X3,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,esk3_0,esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_16])]), c_0_34])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,X1))=X1|~m1_orders_2(X1,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_34]), c_0_15])).
% 0.12/0.37  cnf(c_0_39, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|X2=k1_xboole_0|v2_struct_0(X1)|~m1_orders_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),k3_orders_2(esk2_0,X1,esk1_3(esk2_0,esk3_0,esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (k3_orders_2(esk2_0,esk3_0,esk1_3(esk2_0,esk3_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_33]), c_0_16])])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk1_3(esk2_0,X1,esk3_0),X1)|~m1_orders_2(esk3_0,esk2_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_16]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk1_3(esk2_0,esk3_0,esk3_0),esk3_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_16]), c_0_41])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_33]), c_0_16])]), c_0_34]), c_0_43]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 45
% 0.12/0.37  # Proof object clause steps            : 32
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 28
% 0.12/0.37  # Proof object clause conjectures      : 25
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 17
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 14
% 0.12/0.37  # Proof object simplifying inferences  : 49
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 22
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 22
% 0.12/0.37  # Processed clauses                    : 71
% 0.12/0.37  # ...of these trivial                  : 3
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 64
% 0.12/0.37  # Other redundant clauses eliminated   : 5
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 8
% 0.12/0.37  # Generated clauses                    : 26
% 0.12/0.37  # ...of the previous two non-trivial   : 32
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 22
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 5
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 30
% 0.12/0.37  #    Positive orientable unit clauses  : 10
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 16
% 0.12/0.37  # Current number of unprocessed clauses: 1
% 0.12/0.37  # ...number of literals in the above   : 5
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 30
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 452
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 14
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.37  # Unit Clause-clause subsumption calls : 70
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3038
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
