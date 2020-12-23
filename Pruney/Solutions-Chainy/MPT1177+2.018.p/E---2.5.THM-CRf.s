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
% DateTime   : Thu Dec  3 11:10:07 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 (1160 expanded)
%              Number of clauses        :   49 ( 379 expanded)
%              Number of leaves         :   12 ( 279 expanded)
%              Depth                    :   14
%              Number of atoms          :  330 (8845 expanded)
%              Number of equality atoms :   32 ( 123 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ( r2_xboole_0(X3,X4)
                  <=> m1_orders_2(X3,X1,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(dt_m2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_orders_2(X3,X1,X2)
         => ( v6_orders_2(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

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

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t83_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ( X3 != X4
                   => ( m1_orders_2(X3,X1,X4)
                    <=> ~ m1_orders_2(X4,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t69_orders_2,axiom,(
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

fof(t82_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m2_orders_2(X3,X1,X2)
             => ! [X4] :
                  ( m2_orders_2(X4,X1,X2)
                 => ~ r1_xboole_0(X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(t106_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k4_xboole_0(X2,X3))
     => ( r1_tarski(X1,X2)
        & r1_xboole_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m2_orders_2(X3,X1,X2)
               => ! [X4] :
                    ( m2_orders_2(X4,X1,X2)
                   => ( r2_xboole_0(X3,X4)
                    <=> m1_orders_2(X3,X1,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t84_orders_2])).

fof(c_0_13,plain,(
    ! [X18,X19,X20] :
      ( ( v6_orders_2(X20,X18)
        | ~ m2_orders_2(X20,X18,X19)
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_orders_1(X19,k1_orders_1(u1_struct_0(X18))) )
      & ( m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m2_orders_2(X20,X18,X19)
        | v2_struct_0(X18)
        | ~ v3_orders_2(X18)
        | ~ v4_orders_2(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_orders_1(X19,k1_orders_1(u1_struct_0(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))
    & m2_orders_2(esk3_0,esk1_0,esk2_0)
    & m2_orders_2(esk4_0,esk1_0,esk2_0)
    & ( ~ r2_xboole_0(esk3_0,esk4_0)
      | ~ m1_orders_2(esk3_0,esk1_0,esk4_0) )
    & ( r2_xboole_0(esk3_0,esk4_0)
      | m1_orders_2(esk3_0,esk1_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v3_orders_2(X21)
      | ~ v4_orders_2(X21)
      | ~ v5_orders_2(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | ~ m1_orders_2(X23,X21,X22)
      | r1_tarski(X23,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( m2_orders_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r2_xboole_0(esk3_0,esk4_0)
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_30,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ m1_orders_2(X33,X31,X34)
        | ~ m1_orders_2(X34,X31,X33)
        | X33 = X34
        | ~ m2_orders_2(X34,X31,X32)
        | ~ m2_orders_2(X33,X31,X32)
        | ~ m1_orders_1(X32,k1_orders_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( m1_orders_2(X34,X31,X33)
        | m1_orders_2(X33,X31,X34)
        | X33 = X34
        | ~ m2_orders_2(X34,X31,X32)
        | ~ m2_orders_2(X33,X31,X32)
        | ~ m1_orders_1(X32,k1_orders_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v3_orders_2(X31)
        | ~ v4_orders_2(X31)
        | ~ v5_orders_2(X31)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ m1_orders_2(X1,esk1_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,plain,
    ( m1_orders_2(X1,X2,X3)
    | m1_orders_2(X3,X2,X1)
    | X3 = X1
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X4)
    | ~ m2_orders_2(X3,X2,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( m2_orders_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( X1 = X2
    | m1_orders_2(X1,esk1_0,X2)
    | m1_orders_2(X2,esk1_0,X1)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_xboole_0(esk3_0,esk4_0)
    | ~ m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_41,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ v3_orders_2(X24)
      | ~ v4_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
      | X25 = k1_xboole_0
      | ~ m1_orders_2(X25,X24,X26)
      | ~ m1_orders_2(X26,X24,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).

fof(c_0_42,plain,(
    ! [X15,X16,X17] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ v4_orders_2(X15)
      | ~ v5_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | ~ m1_orders_2(X17,X15,X16)
      | m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk4_0
    | m1_orders_2(esk4_0,esk1_0,X1)
    | m1_orders_2(X1,esk1_0,esk4_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_47,plain,(
    ! [X27,X28,X29,X30] :
      ( v2_struct_0(X27)
      | ~ v3_orders_2(X27)
      | ~ v4_orders_2(X27)
      | ~ v5_orders_2(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
      | ~ m2_orders_2(X29,X27,X28)
      | ~ m2_orders_2(X30,X27,X28)
      | ~ r1_xboole_0(X29,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).

fof(c_0_48,plain,(
    ! [X12,X13,X14] :
      ( ( r1_tarski(X12,X13)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) )
      & ( r1_xboole_0(X12,X14)
        | ~ r1_tarski(X12,k4_xboole_0(X13,X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X10,X11] :
      ( ( k4_xboole_0(X10,X11) != k1_xboole_0
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | k4_xboole_0(X10,X11) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | X2 = k1_xboole_0
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X2,X1,X3)
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ m1_orders_2(X1,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_43]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = esk3_0
    | m1_orders_2(esk4_0,esk1_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_36]),c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( esk4_0 = esk3_0
    | ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_35])).

fof(c_0_56,plain,(
    ! [X7] : ~ r2_xboole_0(X7,X7) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_58,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_tarski(X1,k4_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_63,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( ~ m2_orders_2(X1,esk1_0,esk2_0)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_65,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k4_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_35])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_orders_2(esk3_0,esk1_0,X1)
    | ~ m1_orders_2(X1,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_43]),c_0_17]),c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_62]),c_0_62]),c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ m2_orders_2(X1,esk1_0,esk2_0)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_24])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( ~ m2_orders_2(k1_xboole_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_71]),c_0_72]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:00:20 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.19/0.37  # and selection function SelectNewComplexAHP.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t84_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 0.19/0.37  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.19/0.37  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.19/0.37  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.37  fof(t83_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(X3!=X4=>(m1_orders_2(X3,X1,X4)<=>~(m1_orders_2(X4,X1,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 0.19/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.37  fof(t69_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 0.19/0.37  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 0.19/0.37  fof(t82_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>~(r1_xboole_0(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 0.19/0.37  fof(t106_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k4_xboole_0(X2,X3))=>(r1_tarski(X1,X2)&r1_xboole_0(X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 0.19/0.37  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.19/0.37  fof(irreflexivity_r2_xboole_0, axiom, ![X1, X2]:~(r2_xboole_0(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4))))))), inference(assume_negation,[status(cth)],[t84_orders_2])).
% 0.19/0.37  fof(c_0_13, plain, ![X18, X19, X20]:((v6_orders_2(X20,X18)|~m2_orders_2(X20,X18,X19)|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_orders_1(X19,k1_orders_1(u1_struct_0(X18)))))&(m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m2_orders_2(X20,X18,X19)|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_orders_1(X19,k1_orders_1(u1_struct_0(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.19/0.37  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v4_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))&(m2_orders_2(esk3_0,esk1_0,esk2_0)&(m2_orders_2(esk4_0,esk1_0,esk2_0)&((~r2_xboole_0(esk3_0,esk4_0)|~m1_orders_2(esk3_0,esk1_0,esk4_0))&(r2_xboole_0(esk3_0,esk4_0)|m1_orders_2(esk3_0,esk1_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.37  cnf(c_0_15, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_22, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_orders_2(X23,X21,X22)|r1_tarski(X23,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m2_orders_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (m2_orders_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_25, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.37  cnf(c_0_26, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.37  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r2_xboole_0(esk3_0,esk4_0)|m1_orders_2(esk3_0,esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_30, plain, ![X31, X32, X33, X34]:((~m1_orders_2(X33,X31,X34)|~m1_orders_2(X34,X31,X33)|X33=X34|~m2_orders_2(X34,X31,X32)|~m2_orders_2(X33,X31,X32)|~m1_orders_1(X32,k1_orders_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~l1_orders_2(X31)))&(m1_orders_2(X34,X31,X33)|m1_orders_2(X33,X31,X34)|X33=X34|~m2_orders_2(X34,X31,X32)|~m2_orders_2(X33,X31,X32)|~m1_orders_1(X32,k1_orders_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v3_orders_2(X31)|~v4_orders_2(X31)|~v5_orders_2(X31)|~l1_orders_2(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (r1_tarski(X1,esk4_0)|~m1_orders_2(X1,esk1_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (m1_orders_2(esk3_0,esk1_0,esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.37  cnf(c_0_33, plain, (m1_orders_2(X1,X2,X3)|m1_orders_2(X3,X2,X1)|X3=X1|v2_struct_0(X2)|~m2_orders_2(X1,X2,X4)|~m2_orders_2(X3,X2,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.37  cnf(c_0_34, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (m2_orders_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (X1=X2|m1_orders_2(X1,esk1_0,X2)|m1_orders_2(X2,esk1_0,X1)|~m2_orders_2(X2,esk1_0,esk2_0)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (~r2_xboole_0(esk3_0,esk4_0)|~m1_orders_2(esk3_0,esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (esk4_0=esk3_0|r2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.19/0.37  fof(c_0_40, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.37  fof(c_0_41, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(X25=k1_xboole_0|~m1_orders_2(X25,X24,X26)|~m1_orders_2(X26,X24,X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).
% 0.19/0.37  fof(c_0_42, plain, ![X15, X16, X17]:(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|(~m1_orders_2(X17,X15,X16)|m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_23, c_0_36])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (X1=esk4_0|m1_orders_2(esk4_0,esk1_0,X1)|m1_orders_2(X1,esk1_0,esk4_0)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (esk4_0=esk3_0|~m1_orders_2(esk3_0,esk1_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.37  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  fof(c_0_47, plain, ![X27, X28, X29, X30]:(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|(~m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))|(~m2_orders_2(X29,X27,X28)|(~m2_orders_2(X30,X27,X28)|~r1_xboole_0(X29,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).
% 0.19/0.37  fof(c_0_48, plain, ![X12, X13, X14]:((r1_tarski(X12,X13)|~r1_tarski(X12,k4_xboole_0(X13,X14)))&(r1_xboole_0(X12,X14)|~r1_tarski(X12,k4_xboole_0(X13,X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t106_xboole_1])])])).
% 0.19/0.37  cnf(c_0_49, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  fof(c_0_50, plain, ![X10, X11]:((k4_xboole_0(X10,X11)!=k1_xboole_0|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|k4_xboole_0(X10,X11)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.19/0.37  cnf(c_0_51, plain, (v2_struct_0(X1)|X2=k1_xboole_0|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X2,X1,X3)|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.37  cnf(c_0_52, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,esk3_0)|~m1_orders_2(X1,esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_43]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (esk4_0=esk3_0|m1_orders_2(esk4_0,esk1_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_36]), c_0_45])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (esk4_0=esk3_0|~r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_46, c_0_35])).
% 0.19/0.37  fof(c_0_56, plain, ![X7]:~r2_xboole_0(X7,X7), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).
% 0.19/0.37  cnf(c_0_57, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)|~m2_orders_2(X4,X1,X2)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.37  cnf(c_0_58, plain, (r1_xboole_0(X1,X2)|~r1_tarski(X1,k4_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.37  cnf(c_0_59, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_49])).
% 0.19/0.37  cnf(c_0_60, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.37  cnf(c_0_61, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X3,X2,X1)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)), inference(csr,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.37  cnf(c_0_62, negated_conjecture, (esk4_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.19/0.37  cnf(c_0_63, plain, (~r2_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.37  cnf(c_0_64, negated_conjecture, (~m2_orders_2(X1,esk1_0,esk2_0)|~m2_orders_2(X2,esk1_0,esk2_0)|~r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.37  cnf(c_0_65, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.37  cnf(c_0_66, negated_conjecture, (k4_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_35])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (X1=k1_xboole_0|~m1_orders_2(esk3_0,esk1_0,X1)|~m1_orders_2(X1,esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_43]), c_0_17]), c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.37  cnf(c_0_68, negated_conjecture, (m1_orders_2(esk3_0,esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_62]), c_0_62]), c_0_63])).
% 0.19/0.37  cnf(c_0_69, negated_conjecture, (~m2_orders_2(X1,esk1_0,esk2_0)|~r1_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_24])).
% 0.19/0.37  cnf(c_0_70, negated_conjecture, (r1_xboole_0(k1_xboole_0,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.37  cnf(c_0_71, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_68])])).
% 0.19/0.37  cnf(c_0_72, negated_conjecture, (~m2_orders_2(k1_xboole_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.37  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_71]), c_0_72]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 74
% 0.19/0.37  # Proof object clause steps            : 49
% 0.19/0.37  # Proof object formula steps           : 25
% 0.19/0.37  # Proof object conjectures             : 36
% 0.19/0.37  # Proof object clause conjectures      : 33
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 23
% 0.19/0.37  # Proof object initial formulas used   : 12
% 0.19/0.37  # Proof object generating inferences   : 22
% 0.19/0.37  # Proof object simplifying inferences  : 47
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 29
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 29
% 0.19/0.37  # Processed clauses                    : 139
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 22
% 0.19/0.37  # ...remaining for further processing  : 115
% 0.19/0.37  # Other redundant clauses eliminated   : 3
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 4
% 0.19/0.37  # Backward-rewritten                   : 42
% 0.19/0.37  # Generated clauses                    : 129
% 0.19/0.37  # ...of the previous two non-trivial   : 114
% 0.19/0.37  # Contextual simplify-reflections      : 3
% 0.19/0.37  # Paramodulations                      : 126
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 3
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 39
% 0.19/0.37  #    Positive orientable unit clauses  : 13
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 23
% 0.19/0.37  # Current number of unprocessed clauses: 20
% 0.19/0.37  # ...number of literals in the above   : 38
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 73
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 1029
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 270
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 13
% 0.19/0.37  # Unit Clause-clause subsumption calls : 76
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 17
% 0.19/0.37  # BW rewrite match successes           : 8
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 4692
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.035 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.039 s
% 0.19/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
