%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:11 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (1326 expanded)
%              Number of clauses        :   47 ( 457 expanded)
%              Number of leaves         :    9 ( 321 expanded)
%              Depth                    :   14
%              Number of atoms          :  395 (9411 expanded)
%              Number of equality atoms :   39 ( 274 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(d2_orders_1,axiom,(
    ! [X1] : k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_orders_1)).

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

fof(d16_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v6_orders_2(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ( m2_orders_2(X3,X1,X2)
              <=> ( X3 != k1_xboole_0
                  & r2_wellord1(u1_orders_2(X1),X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,X3)
                       => k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4))) = X4 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_orders_2)).

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

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

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

fof(t57_xboole_1,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_xboole_1)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
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

fof(c_0_11,plain,(
    ! [X17] : k1_orders_1(X17) = k7_subset_1(k1_zfmisc_1(X17),k9_setfam_1(X17),k1_tarski(k1_xboole_0)) ),
    inference(variable_rename,[status(thm)],[d2_orders_1])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))
    & m2_orders_2(esk4_0,esk2_0,esk3_0)
    & m2_orders_2(esk5_0,esk2_0,esk3_0)
    & ( ~ r2_xboole_0(esk4_0,esk5_0)
      | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) )
    & ( r2_xboole_0(esk4_0,esk5_0)
      | m1_orders_2(esk4_0,esk2_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_orders_1(X1) = k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( v2_struct_0(X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_orders_1(esk3_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k9_setfam_1(u1_struct_0(esk2_0)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X12,X13,X14,X15] :
      ( ( X14 != k1_xboole_0
        | ~ m2_orders_2(X14,X12,X13)
        | ~ v6_orders_2(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_wellord1(u1_orders_2(X12),X14)
        | ~ m2_orders_2(X14,X12,X13)
        | ~ v6_orders_2(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X14)
        | k1_funct_1(X13,k1_orders_2(X12,k3_orders_2(X12,X14,X15))) = X15
        | ~ m2_orders_2(X14,X12,X13)
        | ~ v6_orders_2(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X12))
        | X14 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X12),X14)
        | m2_orders_2(X14,X12,X13)
        | ~ v6_orders_2(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X12),X14)
        | m2_orders_2(X14,X12,X13)
        | ~ v6_orders_2(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( k1_funct_1(X13,k1_orders_2(X12,k3_orders_2(X12,X14,esk1_3(X12,X13,X14)))) != esk1_3(X12,X13,X14)
        | X14 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X12),X14)
        | m2_orders_2(X14,X12,X13)
        | ~ v6_orders_2(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

cnf(c_0_25,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ m1_orders_2(X29,X27,X30)
        | ~ m1_orders_2(X30,X27,X29)
        | X29 = X30
        | ~ m2_orders_2(X30,X27,X28)
        | ~ m2_orders_2(X29,X27,X28)
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( m1_orders_2(X30,X27,X29)
        | m1_orders_2(X29,X27,X30)
        | X29 = X30
        | ~ m2_orders_2(X30,X27,X28)
        | ~ m2_orders_2(X29,X27,X28)
        | ~ m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

fof(c_0_27,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_30,plain,
    ( v2_struct_0(X2)
    | X1 != k1_xboole_0
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v2_struct_0(X2)
    | v6_orders_2(X1,X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_32,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_orders_2(X1,esk2_0,X2)
    | ~ m2_orders_2(X2,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_35,plain,(
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

cnf(c_0_36,plain,
    ( v2_struct_0(X2)
    | X1 != k1_xboole_0
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ v6_orders_2(X1,X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_30,c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( v6_orders_2(X1,esk2_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_38,plain,
    ( X1 = X3
    | v2_struct_0(X2)
    | m1_orders_2(X3,X2,X1)
    | m1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m2_orders_2(X3,X2,X4)
    | ~ m2_orders_2(X1,X2,X4)
    | ~ m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ m1_orders_2(X1,esk2_0,X2)
    | ~ m2_orders_2(X2,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( m2_orders_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( X1 = X2
    | m1_orders_2(X2,esk2_0,X1)
    | m1_orders_2(X1,esk2_0,X2)
    | ~ m2_orders_2(X2,esk2_0,esk3_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_44,plain,(
    ! [X7,X8] :
      ( ~ r2_xboole_0(X7,X8)
      | ~ r2_xboole_0(X8,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_xboole_1])])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk5_0
    | r2_xboole_0(X1,esk5_0)
    | ~ m1_orders_2(X1,esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk5_0)
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_orders_2(X2,esk2_0,X1)
    | ~ m1_orders_2(X1,esk2_0,X2)
    | ~ m2_orders_2(X2,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_29]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_29])).

cnf(c_0_49,negated_conjecture,
    ( m2_orders_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( X1 = esk5_0
    | m1_orders_2(X1,esk2_0,esk5_0)
    | m1_orders_2(esk5_0,esk2_0,X1)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_51,plain,
    ( ~ r2_xboole_0(X1,X2)
    | ~ r2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_orders_2(X1,esk2_0,X2)
    | ~ m1_orders_2(X2,esk2_0,X1)
    | ~ m2_orders_2(X1,esk2_0,esk3_0)
    | ~ m2_orders_2(X2,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_29]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( X1 = esk4_0
    | r2_xboole_0(X1,esk4_0)
    | ~ m1_orders_2(X1,esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk5_0,esk2_0,esk4_0)
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ r2_xboole_0(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_orders_2(esk4_0,esk2_0,X1)
    | ~ m1_orders_2(X1,esk2_0,esk4_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,esk5_0)
    | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_60,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_61,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk5_0)
    | ~ m1_orders_2(esk5_0,esk2_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_46]),c_0_40])])).

cnf(c_0_62,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52])).

cnf(c_0_63,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( ~ m1_orders_2(esk4_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_62]),c_0_63])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_62]),c_0_62]),c_0_63]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.031 s
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t84_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 0.20/0.38  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.20/0.38  fof(d2_orders_1, axiom, ![X1]:k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_orders_1)).
% 0.20/0.38  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.20/0.38  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 0.20/0.38  fof(t83_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(X3!=X4=>(m1_orders_2(X3,X1,X4)<=>~(m1_orders_2(X4,X1,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 0.20/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.38  fof(t69_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 0.20/0.38  fof(t57_xboole_1, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&r2_xboole_0(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_xboole_1)).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4))))))), inference(assume_negation,[status(cth)],[t84_orders_2])).
% 0.20/0.38  fof(c_0_10, plain, ![X18, X19, X20]:((v6_orders_2(X20,X18)|~m2_orders_2(X20,X18,X19)|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_orders_1(X19,k1_orders_1(u1_struct_0(X18)))))&(m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m2_orders_2(X20,X18,X19)|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_orders_1(X19,k1_orders_1(u1_struct_0(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.20/0.38  fof(c_0_11, plain, ![X17]:k1_orders_1(X17)=k7_subset_1(k1_zfmisc_1(X17),k9_setfam_1(X17),k1_tarski(k1_xboole_0)), inference(variable_rename,[status(thm)],[d2_orders_1])).
% 0.20/0.38  fof(c_0_12, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk4_0,esk2_0,esk3_0)&(m2_orders_2(esk5_0,esk2_0,esk3_0)&((~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0))&(r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.38  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_14, plain, (k1_orders_1(X1)=k7_subset_1(k1_zfmisc_1(X1),k9_setfam_1(X1),k1_tarski(k1_xboole_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_16, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_orders_2(X23,X21,X22)|r1_tarski(X23,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.20/0.38  cnf(c_0_17, plain, (v2_struct_0(X2)|m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m2_orders_2(X1,X2,X3)|~m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (m1_orders_1(esk3_0,k7_subset_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k9_setfam_1(u1_struct_0(esk2_0)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_15, c_0_14])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  fof(c_0_24, plain, ![X12, X13, X14, X15]:((((X14!=k1_xboole_0|~m2_orders_2(X14,X12,X13)|(~v6_orders_2(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))))|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&(r2_wellord1(u1_orders_2(X12),X14)|~m2_orders_2(X14,X12,X13)|(~v6_orders_2(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))))|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12))))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X14)|k1_funct_1(X13,k1_orders_2(X12,k3_orders_2(X12,X14,X15)))=X15)|~m2_orders_2(X14,X12,X13)|(~v6_orders_2(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))))|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12))))&((m1_subset_1(esk1_3(X12,X13,X14),u1_struct_0(X12))|(X14=k1_xboole_0|~r2_wellord1(u1_orders_2(X12),X14))|m2_orders_2(X14,X12,X13)|(~v6_orders_2(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))))|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&((r2_hidden(esk1_3(X12,X13,X14),X14)|(X14=k1_xboole_0|~r2_wellord1(u1_orders_2(X12),X14))|m2_orders_2(X14,X12,X13)|(~v6_orders_2(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))))|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&(k1_funct_1(X13,k1_orders_2(X12,k3_orders_2(X12,X14,esk1_3(X12,X13,X14))))!=esk1_3(X12,X13,X14)|(X14=k1_xboole_0|~r2_wellord1(u1_orders_2(X12),X14))|m2_orders_2(X14,X12,X13)|(~v6_orders_2(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))))|~m1_orders_1(X13,k1_orders_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.20/0.38  cnf(c_0_25, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  fof(c_0_26, plain, ![X27, X28, X29, X30]:((~m1_orders_2(X29,X27,X30)|~m1_orders_2(X30,X27,X29)|X29=X30|~m2_orders_2(X30,X27,X28)|~m2_orders_2(X29,X27,X28)|~m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)))&(m1_orders_2(X30,X27,X29)|m1_orders_2(X29,X27,X30)|X29=X30|~m2_orders_2(X30,X27,X28)|~m2_orders_2(X29,X27,X28)|~m1_orders_1(X28,k1_orders_1(u1_struct_0(X27)))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).
% 0.20/0.38  fof(c_0_27, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.38  cnf(c_0_28, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_30, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_31, plain, (v2_struct_0(X2)|v6_orders_2(X1,X2)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m2_orders_2(X1,X2,X3)|~m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_25, c_0_14])).
% 0.20/0.38  cnf(c_0_32, plain, (m1_orders_2(X1,X2,X3)|m1_orders_2(X3,X2,X1)|X3=X1|v2_struct_0(X2)|~m2_orders_2(X1,X2,X4)|~m2_orders_2(X3,X2,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.38  cnf(c_0_33, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,X2)|~m1_orders_2(X1,esk2_0,X2)|~m2_orders_2(X2,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.20/0.38  fof(c_0_35, plain, ![X24, X25, X26]:(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))|(X25=k1_xboole_0|~m1_orders_2(X25,X24,X26)|~m1_orders_2(X26,X24,X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).
% 0.20/0.38  cnf(c_0_36, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~v6_orders_2(X1,X2)|~m2_orders_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_30, c_0_14])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (v6_orders_2(X1,esk2_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_38, plain, (X1=X3|v2_struct_0(X2)|m1_orders_2(X3,X2,X1)|m1_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m2_orders_2(X3,X2,X4)|~m2_orders_2(X1,X2,X4)|~m1_orders_1(X4,k7_subset_1(k1_zfmisc_1(u1_struct_0(X2)),k9_setfam_1(u1_struct_0(X2)),k1_tarski(k1_xboole_0)))), inference(rw,[status(thm)],[c_0_32, c_0_14])).
% 0.20/0.38  cnf(c_0_39, negated_conjecture, (X1=X2|r2_xboole_0(X1,X2)|~m1_orders_2(X1,esk2_0,X2)|~m2_orders_2(X2,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_41, plain, (v2_struct_0(X1)|X2=k1_xboole_0|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X2,X1,X3)|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (X1!=k1_xboole_0|~m2_orders_2(X1,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_37])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (X1=X2|m1_orders_2(X2,esk2_0,X1)|m1_orders_2(X1,esk2_0,X2)|~m2_orders_2(X2,esk2_0,esk3_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.20/0.38  fof(c_0_44, plain, ![X7, X8]:(~r2_xboole_0(X7,X8)|~r2_xboole_0(X8,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t57_xboole_1])])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (X1=esk5_0|r2_xboole_0(X1,esk5_0)|~m1_orders_2(X1,esk2_0,esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (X1=k1_xboole_0|~m1_orders_2(X2,esk2_0,X1)|~m1_orders_2(X1,esk2_0,X2)|~m2_orders_2(X2,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_29]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (X1!=k1_xboole_0|~m2_orders_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_29])).
% 0.20/0.38  cnf(c_0_49, negated_conjecture, (m2_orders_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (X1=esk5_0|m1_orders_2(X1,esk2_0,esk5_0)|m1_orders_2(esk5_0,esk2_0,X1)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_43, c_0_40])).
% 0.20/0.38  cnf(c_0_51, plain, (~r2_xboole_0(X1,X2)|~r2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (esk5_0=esk4_0|r2_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (~m1_orders_2(X1,esk2_0,X2)|~m1_orders_2(X2,esk2_0,X1)|~m2_orders_2(X1,esk2_0,esk3_0)|~m2_orders_2(X2,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_29]), c_0_48])).
% 0.20/0.38  cnf(c_0_54, negated_conjecture, (X1=esk4_0|r2_xboole_0(X1,esk4_0)|~m1_orders_2(X1,esk2_0,esk4_0)), inference(spm,[status(thm)],[c_0_39, c_0_49])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk5_0,esk2_0,esk4_0)|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_49])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, (esk5_0=esk4_0|~r2_xboole_0(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (~m1_orders_2(esk4_0,esk2_0,X1)|~m1_orders_2(X1,esk2_0,esk4_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_53, c_0_49])).
% 0.20/0.38  cnf(c_0_58, negated_conjecture, (~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.20/0.38  cnf(c_0_60, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.38  cnf(c_0_61, negated_conjecture, (r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk5_0,esk2_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_46]), c_0_40])])).
% 0.20/0.38  cnf(c_0_62, negated_conjecture, (esk5_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52])).
% 0.20/0.38  cnf(c_0_63, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_60])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (~m1_orders_2(esk4_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_62]), c_0_63])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_62]), c_0_62]), c_0_63]), c_0_64]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 66
% 0.20/0.38  # Proof object clause steps            : 47
% 0.20/0.38  # Proof object formula steps           : 19
% 0.20/0.38  # Proof object conjectures             : 35
% 0.20/0.38  # Proof object clause conjectures      : 32
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 9
% 0.20/0.38  # Proof object generating inferences   : 19
% 0.20/0.38  # Proof object simplifying inferences  : 55
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 10
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 28
% 0.20/0.38  # Removed in clause preprocessing      : 1
% 0.20/0.38  # Initial clauses in saturation        : 27
% 0.20/0.38  # Processed clauses                    : 69
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 5
% 0.20/0.38  # ...remaining for further processing  : 63
% 0.20/0.38  # Other redundant clauses eliminated   : 1
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 2
% 0.20/0.38  # Backward-rewritten                   : 14
% 0.20/0.38  # Generated clauses                    : 56
% 0.20/0.38  # ...of the previous two non-trivial   : 50
% 0.20/0.38  # Contextual simplify-reflections      : 9
% 0.20/0.38  # Paramodulations                      : 47
% 0.20/0.38  # Factorizations                       : 8
% 0.20/0.38  # Equation resolutions                 : 1
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
% 0.20/0.38  # Current number of processed clauses  : 46
% 0.20/0.38  #    Positive orientable unit clauses  : 7
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 4
% 0.20/0.38  #    Non-unit-clauses                  : 35
% 0.20/0.38  # Current number of unprocessed clauses: 3
% 0.20/0.38  # ...number of literals in the above   : 10
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 17
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 578
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 138
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.20/0.38  # Unit Clause-clause subsumption calls : 58
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4739
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.040 s
% 0.20/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
