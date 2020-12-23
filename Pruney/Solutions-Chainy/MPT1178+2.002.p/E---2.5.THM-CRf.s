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
% DateTime   : Thu Dec  3 11:10:12 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 330 expanded)
%              Number of clauses        :   42 ( 115 expanded)
%              Number of leaves         :   11 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  335 (1698 expanded)
%              Number of equality atoms :   43 ( 232 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => r1_tarski(k3_tarski(X1),k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(t31_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t87_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(fc9_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) )
     => ~ v1_xboole_0(k4_orders_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d17_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => ! [X3] :
              ( X3 = k4_orders_2(X1,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X3)
                <=> m2_orders_2(X4,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | r1_tarski(k3_tarski(X15),k3_tarski(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).

fof(c_0_12,plain,(
    ! [X14] : k3_tarski(k1_tarski(X14)) = X14 ),
    inference(variable_rename,[status(thm)],[t31_zfmisc_1])).

cnf(c_0_13,plain,
    ( r1_tarski(k3_tarski(X1),k3_tarski(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,plain,
    ( k3_tarski(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_15,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(pm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X12,X13] :
      ( ( ~ r1_tarski(k1_tarski(X12),X13)
        | r2_hidden(X12,X13) )
      & ( ~ r2_hidden(X12,X13)
        | r1_tarski(k1_tarski(X12),X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
           => k3_tarski(k4_orders_2(X1,X2)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t87_orders_2])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | k1_tarski(X1) != X2 ),
    inference(pm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))
    & k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_24,plain,(
    ! [X32,X33] :
      ( v2_struct_0(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_orders_1(X33,k1_orders_1(u1_struct_0(X32)))
      | ~ v1_xboole_0(k4_orders_2(X32,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_25,plain,
    ( X1 = k3_tarski(X2)
    | k1_tarski(X1) != X2
    | ~ r1_tarski(k3_tarski(X2),X1) ),
    inference(pm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(pm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(pm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X19 != k1_xboole_0
        | ~ m2_orders_2(X19,X17,X18)
        | ~ v6_orders_2(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_wellord1(u1_orders_2(X17),X19)
        | ~ m2_orders_2(X19,X17,X18)
        | ~ v6_orders_2(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ r2_hidden(X20,X19)
        | k1_funct_1(X18,k1_orders_2(X17,k3_orders_2(X17,X19,X20))) = X20
        | ~ m2_orders_2(X19,X17,X18)
        | ~ v6_orders_2(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk2_3(X17,X18,X19),u1_struct_0(X17))
        | X19 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X17),X19)
        | m2_orders_2(X19,X17,X18)
        | ~ v6_orders_2(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X17),X19)
        | m2_orders_2(X19,X17,X18)
        | ~ v6_orders_2(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( k1_funct_1(X18,k1_orders_2(X17,k3_orders_2(X17,X19,esk2_3(X17,X18,X19)))) != esk2_3(X17,X18,X19)
        | X19 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X17),X19)
        | m2_orders_2(X19,X17,X18)
        | ~ v6_orders_2(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v3_orders_2(X17)
        | ~ v4_orders_2(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_38,plain,(
    ! [X29,X30,X31] :
      ( ( v6_orders_2(X31,X29)
        | ~ m2_orders_2(X31,X29,X30)
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29))) )
      & ( m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m2_orders_2(X31,X29,X30)
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29)
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

cnf(c_0_39,plain,
    ( X1 = k3_tarski(X2)
    | k1_tarski(X1) != X2
    | ~ r1_tarski(X2,k1_tarski(X1)) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(X1,k1_xboole_0)
    | ~ r2_hidden(X1,k4_orders_2(esk4_0,esk5_0)) ),
    inference(pm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(k4_orders_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

fof(c_0_43,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_44,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( X1 = k3_tarski(X2)
    | k1_tarski(X1) != X2 ),
    inference(pm,[status(thm)],[c_0_39,c_0_17])).

fof(c_0_47,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X25,X24)
        | m2_orders_2(X25,X22,X23)
        | X24 != k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ m2_orders_2(X26,X22,X23)
        | r2_hidden(X26,X24)
        | X24 != k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( ~ r2_hidden(esk3_3(X22,X23,X27),X27)
        | ~ m2_orders_2(esk3_3(X22,X23,X27),X22,X23)
        | X27 = k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk3_3(X22,X23,X27),X27)
        | m2_orders_2(esk3_3(X22,X23,X27),X22,X23)
        | X27 = k4_orders_2(X22,X23)
        | ~ m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))
        | v2_struct_0(X22)
        | ~ v3_orders_2(X22)
        | ~ v4_orders_2(X22)
        | ~ v5_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk1_1(k4_orders_2(esk4_0,esk5_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | X2 != k1_xboole_0
    | ~ m2_orders_2(X2,X1,X3)
    | ~ m2_orders_2(X2,X1,X4)
    | ~ v6_orders_2(X2,X1)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(pm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( m1_orders_1(esk5_0,k1_orders_1(k3_tarski(X1)))
    | k1_tarski(u1_struct_0(esk4_0)) != X1 ),
    inference(pm,[status(thm)],[c_0_31,c_0_46])).

cnf(c_0_53,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( esk1_1(k4_orders_2(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_20,c_0_48]),c_0_49])])).

cnf(c_0_55,negated_conjecture,
    ( v6_orders_2(X1,esk4_0)
    | ~ m2_orders_2(X1,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk4_0,esk5_0)
    | ~ m2_orders_2(X1,esk4_0,X2)
    | ~ v6_orders_2(X1,esk4_0)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_57,negated_conjecture,
    ( m1_orders_1(esk5_0,k1_orders_1(X1))
    | k1_tarski(u1_struct_0(esk4_0)) != k1_tarski(X1) ),
    inference(pm,[status(thm)],[c_0_52,c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( m2_orders_2(X1,esk4_0,esk5_0)
    | X2 != k4_orders_2(esk4_0,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k4_orders_2(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_54]),c_0_42])).

cnf(c_0_60,negated_conjecture,
    ( v6_orders_2(X1,esk4_0)
    | X2 != k4_orders_2(esk4_0,esk5_0)
    | ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_53]),c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ m2_orders_2(X1,esk4_0,esk5_0)
    | ~ v6_orders_2(X1,esk4_0) ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk4_0,esk5_0) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v6_orders_2(k1_xboole_0,esk4_0) ),
    inference(pm,[status(thm)],[c_0_60,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61,c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:09:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.29/2.53  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 2.29/2.53  # and selection function NoSelection.
% 2.29/2.53  #
% 2.29/2.53  # Preprocessing time       : 0.028 s
% 2.29/2.53  
% 2.29/2.53  # Proof found!
% 2.29/2.53  # SZS status Theorem
% 2.29/2.53  # SZS output start CNFRefutation
% 2.29/2.53  fof(t95_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>r1_tarski(k3_tarski(X1),k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.29/2.53  fof(t31_zfmisc_1, axiom, ![X1]:k3_tarski(k1_tarski(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.29/2.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.29/2.53  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.29/2.53  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.29/2.53  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.29/2.53  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.29/2.53  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 2.29/2.53  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 2.29/2.53  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.29/2.53  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.29/2.53  fof(c_0_11, plain, ![X15, X16]:(~r1_tarski(X15,X16)|r1_tarski(k3_tarski(X15),k3_tarski(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_zfmisc_1])])).
% 2.29/2.53  fof(c_0_12, plain, ![X14]:k3_tarski(k1_tarski(X14))=X14, inference(variable_rename,[status(thm)],[t31_zfmisc_1])).
% 2.29/2.53  cnf(c_0_13, plain, (r1_tarski(k3_tarski(X1),k3_tarski(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.29/2.53  cnf(c_0_14, plain, (k3_tarski(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.29/2.53  fof(c_0_15, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.29/2.53  cnf(c_0_16, plain, (r1_tarski(X1,k3_tarski(X2))|~r1_tarski(k1_tarski(X1),X2)), inference(pm,[status(thm)],[c_0_13, c_0_14])).
% 2.29/2.53  cnf(c_0_17, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.29/2.53  fof(c_0_18, plain, ![X12, X13]:((~r1_tarski(k1_tarski(X12),X13)|r2_hidden(X12,X13))&(~r2_hidden(X12,X13)|r1_tarski(k1_tarski(X12),X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 2.29/2.53  fof(c_0_19, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 2.29/2.53  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 2.29/2.53  cnf(c_0_21, plain, (r1_tarski(X1,k3_tarski(X2))|k1_tarski(X1)!=X2), inference(pm,[status(thm)],[c_0_16, c_0_17])).
% 2.29/2.53  cnf(c_0_22, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 2.29/2.53  fof(c_0_23, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))&k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 2.29/2.53  fof(c_0_24, plain, ![X32, X33]:(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|~m1_orders_1(X33,k1_orders_1(u1_struct_0(X32)))|~v1_xboole_0(k4_orders_2(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 2.29/2.53  cnf(c_0_25, plain, (X1=k3_tarski(X2)|k1_tarski(X1)!=X2|~r1_tarski(k3_tarski(X2),X1)), inference(pm,[status(thm)],[c_0_20, c_0_21])).
% 2.29/2.53  cnf(c_0_26, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(X1,k1_tarski(X2))), inference(pm,[status(thm)],[c_0_13, c_0_14])).
% 2.29/2.53  cnf(c_0_27, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(pm,[status(thm)],[c_0_16, c_0_22])).
% 2.29/2.53  cnf(c_0_28, negated_conjecture, (k3_tarski(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  fof(c_0_29, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 2.29/2.53  cnf(c_0_30, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.29/2.53  cnf(c_0_31, negated_conjecture, (m1_orders_1(esk5_0,k1_orders_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  cnf(c_0_32, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  cnf(c_0_33, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  cnf(c_0_34, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  cnf(c_0_35, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.29/2.53  fof(c_0_37, plain, ![X17, X18, X19, X20]:((((X19!=k1_xboole_0|~m2_orders_2(X19,X17,X18)|(~v6_orders_2(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))))|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)))&(r2_wellord1(u1_orders_2(X17),X19)|~m2_orders_2(X19,X17,X18)|(~v6_orders_2(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))))|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17))))&(~m1_subset_1(X20,u1_struct_0(X17))|(~r2_hidden(X20,X19)|k1_funct_1(X18,k1_orders_2(X17,k3_orders_2(X17,X19,X20)))=X20)|~m2_orders_2(X19,X17,X18)|(~v6_orders_2(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))))|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17))))&((m1_subset_1(esk2_3(X17,X18,X19),u1_struct_0(X17))|(X19=k1_xboole_0|~r2_wellord1(u1_orders_2(X17),X19))|m2_orders_2(X19,X17,X18)|(~v6_orders_2(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))))|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)))&((r2_hidden(esk2_3(X17,X18,X19),X19)|(X19=k1_xboole_0|~r2_wellord1(u1_orders_2(X17),X19))|m2_orders_2(X19,X17,X18)|(~v6_orders_2(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))))|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)))&(k1_funct_1(X18,k1_orders_2(X17,k3_orders_2(X17,X19,esk2_3(X17,X18,X19))))!=esk2_3(X17,X18,X19)|(X19=k1_xboole_0|~r2_wellord1(u1_orders_2(X17),X19))|m2_orders_2(X19,X17,X18)|(~v6_orders_2(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))))|~m1_orders_1(X18,k1_orders_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 2.29/2.53  fof(c_0_38, plain, ![X29, X30, X31]:((v6_orders_2(X31,X29)|~m2_orders_2(X31,X29,X30)|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))))&(m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|~m2_orders_2(X31,X29,X30)|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 2.29/2.53  cnf(c_0_39, plain, (X1=k3_tarski(X2)|k1_tarski(X1)!=X2|~r1_tarski(X2,k1_tarski(X1))), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 2.29/2.53  cnf(c_0_40, negated_conjecture, (r1_tarski(X1,k1_xboole_0)|~r2_hidden(X1,k4_orders_2(esk4_0,esk5_0))), inference(pm,[status(thm)],[c_0_27, c_0_28])).
% 2.29/2.53  cnf(c_0_41, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.29/2.53  cnf(c_0_42, negated_conjecture, (~v1_xboole_0(k4_orders_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 2.29/2.53  fof(c_0_43, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 2.29/2.53  cnf(c_0_44, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.29/2.53  cnf(c_0_45, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.29/2.53  cnf(c_0_46, plain, (X1=k3_tarski(X2)|k1_tarski(X1)!=X2), inference(pm,[status(thm)],[c_0_39, c_0_17])).
% 2.29/2.53  fof(c_0_47, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X25,X24)|m2_orders_2(X25,X22,X23)|X24!=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)))&(~m2_orders_2(X26,X22,X23)|r2_hidden(X26,X24)|X24!=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22))))&((~r2_hidden(esk3_3(X22,X23,X27),X27)|~m2_orders_2(esk3_3(X22,X23,X27),X22,X23)|X27=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)))&(r2_hidden(esk3_3(X22,X23,X27),X27)|m2_orders_2(esk3_3(X22,X23,X27),X22,X23)|X27=k4_orders_2(X22,X23)|~m1_orders_1(X23,k1_orders_1(u1_struct_0(X22)))|(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 2.29/2.53  cnf(c_0_48, negated_conjecture, (r1_tarski(esk1_1(k4_orders_2(esk4_0,esk5_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 2.29/2.53  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 2.29/2.53  cnf(c_0_50, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.29/2.53  cnf(c_0_51, plain, (v2_struct_0(X1)|X2!=k1_xboole_0|~m2_orders_2(X2,X1,X3)|~m2_orders_2(X2,X1,X4)|~v6_orders_2(X2,X1)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X1)))|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(pm,[status(thm)],[c_0_44, c_0_45])).
% 2.29/2.53  cnf(c_0_52, negated_conjecture, (m1_orders_1(esk5_0,k1_orders_1(k3_tarski(X1)))|k1_tarski(u1_struct_0(esk4_0))!=X1), inference(pm,[status(thm)],[c_0_31, c_0_46])).
% 2.29/2.53  cnf(c_0_53, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 2.29/2.53  cnf(c_0_54, negated_conjecture, (esk1_1(k4_orders_2(esk4_0,esk5_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_20, c_0_48]), c_0_49])])).
% 2.29/2.53  cnf(c_0_55, negated_conjecture, (v6_orders_2(X1,esk4_0)|~m2_orders_2(X1,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 2.29/2.53  cnf(c_0_56, negated_conjecture, (X1!=k1_xboole_0|~m2_orders_2(X1,esk4_0,esk5_0)|~m2_orders_2(X1,esk4_0,X2)|~v6_orders_2(X1,esk4_0)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 2.29/2.53  cnf(c_0_57, negated_conjecture, (m1_orders_1(esk5_0,k1_orders_1(X1))|k1_tarski(u1_struct_0(esk4_0))!=k1_tarski(X1)), inference(pm,[status(thm)],[c_0_52, c_0_14])).
% 2.29/2.53  cnf(c_0_58, negated_conjecture, (m2_orders_2(X1,esk4_0,esk5_0)|X2!=k4_orders_2(esk4_0,esk5_0)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 2.29/2.53  cnf(c_0_59, negated_conjecture, (r2_hidden(k1_xboole_0,k4_orders_2(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_54]), c_0_42])).
% 2.29/2.53  cnf(c_0_60, negated_conjecture, (v6_orders_2(X1,esk4_0)|X2!=k4_orders_2(esk4_0,esk5_0)|~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_53]), c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 2.29/2.53  cnf(c_0_61, negated_conjecture, (X1!=k1_xboole_0|~m2_orders_2(X1,esk4_0,esk5_0)|~v6_orders_2(X1,esk4_0)), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 2.29/2.53  cnf(c_0_62, negated_conjecture, (m2_orders_2(k1_xboole_0,esk4_0,esk5_0)), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 2.29/2.53  cnf(c_0_63, negated_conjecture, (v6_orders_2(k1_xboole_0,esk4_0)), inference(pm,[status(thm)],[c_0_60, c_0_59])).
% 2.29/2.53  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61, c_0_62]), c_0_63])]), ['proof']).
% 2.29/2.53  # SZS output end CNFRefutation
% 2.29/2.53  # Proof object total steps             : 65
% 2.29/2.53  # Proof object clause steps            : 42
% 2.29/2.53  # Proof object formula steps           : 23
% 2.29/2.53  # Proof object conjectures             : 25
% 2.29/2.53  # Proof object clause conjectures      : 22
% 2.29/2.53  # Proof object formula conjectures     : 3
% 2.29/2.53  # Proof object initial clauses used    : 19
% 2.29/2.53  # Proof object initial formulas used   : 11
% 2.29/2.53  # Proof object generating inferences   : 23
% 2.29/2.53  # Proof object simplifying inferences  : 37
% 2.29/2.53  # Training examples: 0 positive, 0 negative
% 2.29/2.53  # Parsed axioms                        : 11
% 2.29/2.53  # Removed by relevancy pruning/SinE    : 0
% 2.29/2.53  # Initial clauses                      : 30
% 2.29/2.53  # Removed in clause preprocessing      : 0
% 2.29/2.53  # Initial clauses in saturation        : 30
% 2.29/2.53  # Processed clauses                    : 18926
% 2.29/2.53  # ...of these trivial                  : 435
% 2.29/2.53  # ...subsumed                          : 16303
% 2.29/2.53  # ...remaining for further processing  : 2188
% 2.29/2.53  # Other redundant clauses eliminated   : 0
% 2.29/2.53  # Clauses deleted for lack of memory   : 0
% 2.29/2.53  # Backward-subsumed                    : 301
% 2.29/2.53  # Backward-rewritten                   : 509
% 2.29/2.53  # Generated clauses                    : 372080
% 2.29/2.53  # ...of the previous two non-trivial   : 246025
% 2.29/2.53  # Contextual simplify-reflections      : 0
% 2.29/2.53  # Paramodulations                      : 371558
% 2.29/2.53  # Factorizations                       : 10
% 2.29/2.53  # Equation resolutions                 : 326
% 2.29/2.53  # Propositional unsat checks           : 0
% 2.29/2.53  #    Propositional check models        : 0
% 2.29/2.53  #    Propositional check unsatisfiable : 0
% 2.29/2.53  #    Propositional clauses             : 0
% 2.29/2.53  #    Propositional clauses after purity: 0
% 2.29/2.53  #    Propositional unsat core size     : 0
% 2.29/2.53  #    Propositional preprocessing time  : 0.000
% 2.29/2.53  #    Propositional encoding time       : 0.000
% 2.29/2.53  #    Propositional solver time         : 0.000
% 2.29/2.53  #    Success case prop preproc time    : 0.000
% 2.29/2.53  #    Success case prop encoding time   : 0.000
% 2.29/2.53  #    Success case prop solver time     : 0.000
% 2.29/2.53  # Current number of processed clauses  : 1192
% 2.29/2.53  #    Positive orientable unit clauses  : 29
% 2.29/2.53  #    Positive unorientable unit clauses: 0
% 2.29/2.53  #    Negative unit clauses             : 5
% 2.29/2.53  #    Non-unit-clauses                  : 1158
% 2.29/2.53  # Current number of unprocessed clauses: 222099
% 2.29/2.53  # ...number of literals in the above   : 997871
% 2.29/2.53  # Current number of archived formulas  : 0
% 2.29/2.53  # Current number of archived clauses   : 996
% 2.29/2.53  # Clause-clause subsumption calls (NU) : 1235274
% 2.29/2.53  # Rec. Clause-clause subsumption calls : 859442
% 2.29/2.53  # Non-unit clause-clause subsumptions  : 14462
% 2.29/2.53  # Unit Clause-clause subsumption calls : 3026
% 2.29/2.53  # Rewrite failures with RHS unbound    : 0
% 2.29/2.53  # BW rewrite match attempts            : 157
% 2.29/2.53  # BW rewrite match successes           : 22
% 2.29/2.53  # Condensation attempts                : 0
% 2.29/2.53  # Condensation successes               : 0
% 2.29/2.53  # Termbank termtop insertions          : 3149346
% 2.38/2.54  
% 2.38/2.54  # -------------------------------------------------
% 2.38/2.54  # User time                : 2.111 s
% 2.38/2.54  # System time              : 0.093 s
% 2.38/2.54  # Total time               : 2.203 s
% 2.38/2.54  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
