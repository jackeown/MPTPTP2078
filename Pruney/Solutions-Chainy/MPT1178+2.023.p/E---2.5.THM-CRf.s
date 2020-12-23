%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:15 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 118 expanded)
%              Number of clauses        :   27 (  41 expanded)
%              Number of leaves         :    9 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  296 ( 719 expanded)
%              Number of equality atoms :   44 ( 101 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t91_orders_1,axiom,(
    ! [X1] :
      ( ~ ( ? [X2] :
              ( X2 != k1_xboole_0
              & r2_hidden(X2,X1) )
          & k3_tarski(X1) = k1_xboole_0 )
      & ~ ( k3_tarski(X1) != k1_xboole_0
          & ! [X2] :
              ~ ( X2 != k1_xboole_0
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

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

fof(c_0_9,plain,(
    ! [X25,X26,X27] :
      ( ( X26 = k1_xboole_0
        | ~ r2_hidden(X26,X25)
        | k3_tarski(X25) != k1_xboole_0 )
      & ( esk4_1(X27) != k1_xboole_0
        | k3_tarski(X27) = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X27),X27)
        | k3_tarski(X27) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_10,plain,(
    ! [X6] :
      ( X6 = k1_xboole_0
      | r2_hidden(esk1_1(X6),X6) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X16,X15)
        | m2_orders_2(X16,X13,X14)
        | X15 != k4_orders_2(X13,X14)
        | ~ m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ m2_orders_2(X17,X13,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_orders_2(X13,X14)
        | ~ m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r2_hidden(esk3_3(X13,X14,X18),X18)
        | ~ m2_orders_2(esk3_3(X13,X14,X18),X13,X14)
        | X18 = k4_orders_2(X13,X14)
        | ~ m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk3_3(X13,X14,X18),X18)
        | m2_orders_2(esk3_3(X13,X14,X18),X13,X14)
        | X18 = k4_orders_2(X13,X14)
        | ~ m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ v5_orders_2(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))
    & k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_20,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( esk1_1(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0
    | k4_orders_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_30,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X10 != k1_xboole_0
        | ~ m2_orders_2(X10,X8,X9)
        | ~ v6_orders_2(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_wellord1(u1_orders_2(X8),X10)
        | ~ m2_orders_2(X10,X8,X9)
        | ~ v6_orders_2(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r2_hidden(X11,X10)
        | k1_funct_1(X9,k1_orders_2(X8,k3_orders_2(X8,X10,X11))) = X11
        | ~ m2_orders_2(X10,X8,X9)
        | ~ v6_orders_2(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk2_3(X8,X9,X10),u1_struct_0(X8))
        | X10 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X8),X10)
        | m2_orders_2(X10,X8,X9)
        | ~ v6_orders_2(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_hidden(esk2_3(X8,X9,X10),X10)
        | X10 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X8),X10)
        | m2_orders_2(X10,X8,X9)
        | ~ v6_orders_2(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( k1_funct_1(X9,k1_orders_2(X8,k3_orders_2(X8,X10,esk2_3(X8,X9,X10)))) != esk2_3(X8,X9,X10)
        | X10 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X8),X10)
        | m2_orders_2(X10,X8,X9)
        | ~ v6_orders_2(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))
        | v2_struct_0(X8)
        | ~ v3_orders_2(X8)
        | ~ v4_orders_2(X8)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_31,plain,(
    ! [X20,X21,X22] :
      ( ( v6_orders_2(X22,X20)
        | ~ m2_orders_2(X22,X20,X21)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_orders_1(X21,k1_orders_1(u1_struct_0(X20))) )
      & ( m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ m2_orders_2(X22,X20,X21)
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_orders_1(X21,k1_orders_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_32,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v3_orders_2(X23)
      | ~ v4_orders_2(X23)
      | ~ v5_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))
      | ~ v1_xboole_0(k4_orders_2(X23,X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_33,negated_conjecture,
    ( m2_orders_2(X1,esk5_0,esk6_0)
    | ~ r2_hidden(X1,k4_orders_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k4_orders_2(esk5_0,esk6_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k4_orders_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_27])).

cnf(c_0_35,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k4_orders_2(esk5_0,esk6_0) = k1_xboole_0
    | m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_35])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | ~ m2_orders_2(k1_xboole_0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_41])]),c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_21]),c_0_43]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.22/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.22/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.22/0.39  #
% 0.22/0.39  # Preprocessing time       : 0.029 s
% 0.22/0.39  # Presaturation interreduction done
% 0.22/0.39  
% 0.22/0.39  # Proof found!
% 0.22/0.39  # SZS status Theorem
% 0.22/0.39  # SZS output start CNFRefutation
% 0.22/0.39  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.22/0.39  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.22/0.39  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 0.22/0.39  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 0.22/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.22/0.39  fof(dt_o_0_0_xboole_0, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 0.22/0.39  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 0.22/0.39  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.22/0.39  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.22/0.39  fof(c_0_9, plain, ![X25, X26, X27]:((X26=k1_xboole_0|~r2_hidden(X26,X25)|k3_tarski(X25)!=k1_xboole_0)&((esk4_1(X27)!=k1_xboole_0|k3_tarski(X27)=k1_xboole_0)&(r2_hidden(esk4_1(X27),X27)|k3_tarski(X27)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.22/0.39  fof(c_0_10, plain, ![X6]:(X6=k1_xboole_0|r2_hidden(esk1_1(X6),X6)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.22/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.22/0.39  fof(c_0_12, plain, ![X13, X14, X15, X16, X17, X18]:(((~r2_hidden(X16,X15)|m2_orders_2(X16,X13,X14)|X15!=k4_orders_2(X13,X14)|~m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v3_orders_2(X13)|~v4_orders_2(X13)|~v5_orders_2(X13)|~l1_orders_2(X13)))&(~m2_orders_2(X17,X13,X14)|r2_hidden(X17,X15)|X15!=k4_orders_2(X13,X14)|~m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v3_orders_2(X13)|~v4_orders_2(X13)|~v5_orders_2(X13)|~l1_orders_2(X13))))&((~r2_hidden(esk3_3(X13,X14,X18),X18)|~m2_orders_2(esk3_3(X13,X14,X18),X13,X14)|X18=k4_orders_2(X13,X14)|~m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v3_orders_2(X13)|~v4_orders_2(X13)|~v5_orders_2(X13)|~l1_orders_2(X13)))&(r2_hidden(esk3_3(X13,X14,X18),X18)|m2_orders_2(esk3_3(X13,X14,X18),X13,X14)|X18=k4_orders_2(X13,X14)|~m1_orders_1(X14,k1_orders_1(u1_struct_0(X13)))|(v2_struct_0(X13)|~v3_orders_2(X13)|~v4_orders_2(X13)|~v5_orders_2(X13)|~l1_orders_2(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.22/0.39  cnf(c_0_13, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.22/0.39  cnf(c_0_14, plain, (X1=k1_xboole_0|r2_hidden(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.22/0.39  fof(c_0_15, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))&k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.22/0.39  cnf(c_0_16, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.39  cnf(c_0_17, plain, (esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|k3_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.22/0.39  cnf(c_0_18, negated_conjecture, (k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  fof(c_0_19, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.22/0.39  cnf(c_0_20, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_16])).
% 0.22/0.39  cnf(c_0_21, negated_conjecture, (m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_23, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_24, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_25, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.39  cnf(c_0_27, negated_conjecture, (esk1_1(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0|k4_orders_2(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.22/0.39  cnf(c_0_28, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.22/0.39  cnf(c_0_29, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).
% 0.22/0.39  fof(c_0_30, plain, ![X8, X9, X10, X11]:((((X10!=k1_xboole_0|~m2_orders_2(X10,X8,X9)|(~v6_orders_2(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))))|~m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))&(r2_wellord1(u1_orders_2(X8),X10)|~m2_orders_2(X10,X8,X9)|(~v6_orders_2(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))))|~m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))&(~m1_subset_1(X11,u1_struct_0(X8))|(~r2_hidden(X11,X10)|k1_funct_1(X9,k1_orders_2(X8,k3_orders_2(X8,X10,X11)))=X11)|~m2_orders_2(X10,X8,X9)|(~v6_orders_2(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))))|~m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8))))&((m1_subset_1(esk2_3(X8,X9,X10),u1_struct_0(X8))|(X10=k1_xboole_0|~r2_wellord1(u1_orders_2(X8),X10))|m2_orders_2(X10,X8,X9)|(~v6_orders_2(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))))|~m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))&((r2_hidden(esk2_3(X8,X9,X10),X10)|(X10=k1_xboole_0|~r2_wellord1(u1_orders_2(X8),X10))|m2_orders_2(X10,X8,X9)|(~v6_orders_2(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))))|~m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))&(k1_funct_1(X9,k1_orders_2(X8,k3_orders_2(X8,X10,esk2_3(X8,X9,X10))))!=esk2_3(X8,X9,X10)|(X10=k1_xboole_0|~r2_wellord1(u1_orders_2(X8),X10))|m2_orders_2(X10,X8,X9)|(~v6_orders_2(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8))))|~m1_orders_1(X9,k1_orders_1(u1_struct_0(X8)))|(v2_struct_0(X8)|~v3_orders_2(X8)|~v4_orders_2(X8)|~v5_orders_2(X8)|~l1_orders_2(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.22/0.39  fof(c_0_31, plain, ![X20, X21, X22]:((v6_orders_2(X22,X20)|~m2_orders_2(X22,X20,X21)|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_orders_1(X21,k1_orders_1(u1_struct_0(X20)))))&(m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|~m2_orders_2(X22,X20,X21)|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_orders_1(X21,k1_orders_1(u1_struct_0(X20)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.22/0.39  fof(c_0_32, plain, ![X23, X24]:(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))|~v1_xboole_0(k4_orders_2(X23,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.22/0.39  cnf(c_0_33, negated_conjecture, (m2_orders_2(X1,esk5_0,esk6_0)|~r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26])).
% 0.22/0.39  cnf(c_0_34, negated_conjecture, (k4_orders_2(esk5_0,esk6_0)=k1_xboole_0|r2_hidden(k1_xboole_0,k4_orders_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_14, c_0_27])).
% 0.22/0.39  cnf(c_0_35, plain, (o_0_0_xboole_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.22/0.39  cnf(c_0_36, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.22/0.39  cnf(c_0_37, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.22/0.39  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.22/0.39  cnf(c_0_39, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.22/0.39  cnf(c_0_40, negated_conjecture, (k4_orders_2(esk5_0,esk6_0)=k1_xboole_0|m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.22/0.39  cnf(c_0_41, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_29, c_0_35])).
% 0.22/0.39  cnf(c_0_42, plain, (v2_struct_0(X1)|~m2_orders_2(k1_xboole_0,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.22/0.39  cnf(c_0_43, negated_conjecture, (m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_41])]), c_0_26])).
% 0.22/0.39  cnf(c_0_44, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_21]), c_0_43]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), ['proof']).
% 0.22/0.39  # SZS output end CNFRefutation
% 0.22/0.39  # Proof object total steps             : 45
% 0.22/0.39  # Proof object clause steps            : 27
% 0.22/0.39  # Proof object formula steps           : 18
% 0.22/0.39  # Proof object conjectures             : 16
% 0.22/0.39  # Proof object clause conjectures      : 13
% 0.22/0.39  # Proof object formula conjectures     : 3
% 0.22/0.39  # Proof object initial clauses used    : 16
% 0.22/0.39  # Proof object initial formulas used   : 9
% 0.22/0.39  # Proof object generating inferences   : 8
% 0.22/0.39  # Proof object simplifying inferences  : 26
% 0.22/0.39  # Training examples: 0 positive, 0 negative
% 0.22/0.39  # Parsed axioms                        : 9
% 0.22/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.39  # Initial clauses                      : 26
% 0.22/0.39  # Removed in clause preprocessing      : 0
% 0.22/0.39  # Initial clauses in saturation        : 26
% 0.22/0.39  # Processed clauses                    : 60
% 0.22/0.39  # ...of these trivial                  : 0
% 0.22/0.39  # ...subsumed                          : 1
% 0.22/0.39  # ...remaining for further processing  : 59
% 0.22/0.39  # Other redundant clauses eliminated   : 3
% 0.22/0.39  # Clauses deleted for lack of memory   : 0
% 0.22/0.39  # Backward-subsumed                    : 0
% 0.22/0.39  # Backward-rewritten                   : 2
% 0.22/0.39  # Generated clauses                    : 22
% 0.22/0.39  # ...of the previous two non-trivial   : 18
% 0.22/0.39  # Contextual simplify-reflections      : 6
% 0.22/0.39  # Paramodulations                      : 19
% 0.22/0.39  # Factorizations                       : 0
% 0.22/0.39  # Equation resolutions                 : 3
% 0.22/0.39  # Propositional unsat checks           : 0
% 0.22/0.39  #    Propositional check models        : 0
% 0.22/0.39  #    Propositional check unsatisfiable : 0
% 0.22/0.39  #    Propositional clauses             : 0
% 0.22/0.39  #    Propositional clauses after purity: 0
% 0.22/0.39  #    Propositional unsat core size     : 0
% 0.22/0.39  #    Propositional preprocessing time  : 0.000
% 0.22/0.39  #    Propositional encoding time       : 0.000
% 0.22/0.39  #    Propositional solver time         : 0.000
% 0.22/0.39  #    Success case prop preproc time    : 0.000
% 0.22/0.39  #    Success case prop encoding time   : 0.000
% 0.22/0.39  #    Success case prop solver time     : 0.000
% 0.22/0.39  # Current number of processed clauses  : 28
% 0.22/0.39  #    Positive orientable unit clauses  : 9
% 0.22/0.39  #    Positive unorientable unit clauses: 0
% 0.22/0.39  #    Negative unit clauses             : 1
% 0.22/0.39  #    Non-unit-clauses                  : 18
% 0.22/0.39  # Current number of unprocessed clauses: 8
% 0.22/0.39  # ...number of literals in the above   : 80
% 0.22/0.39  # Current number of archived formulas  : 0
% 0.22/0.39  # Current number of archived clauses   : 28
% 0.22/0.39  # Clause-clause subsumption calls (NU) : 539
% 0.22/0.39  # Rec. Clause-clause subsumption calls : 23
% 0.22/0.39  # Non-unit clause-clause subsumptions  : 7
% 0.22/0.39  # Unit Clause-clause subsumption calls : 3
% 0.22/0.39  # Rewrite failures with RHS unbound    : 0
% 0.22/0.39  # BW rewrite match attempts            : 2
% 0.22/0.39  # BW rewrite match successes           : 2
% 0.22/0.39  # Condensation attempts                : 0
% 0.22/0.39  # Condensation successes               : 0
% 0.22/0.39  # Termbank termtop insertions          : 3468
% 0.22/0.39  
% 0.22/0.39  # -------------------------------------------------
% 0.22/0.39  # User time                : 0.032 s
% 0.22/0.39  # System time              : 0.004 s
% 0.22/0.39  # Total time               : 0.037 s
% 0.22/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
