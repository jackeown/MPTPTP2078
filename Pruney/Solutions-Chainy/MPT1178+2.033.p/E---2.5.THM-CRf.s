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
% DateTime   : Thu Dec  3 11:10:16 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 111 expanded)
%              Number of clauses        :   24 (  37 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  297 ( 727 expanded)
%              Number of equality atoms :   45 ( 107 expanded)
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

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_8,plain,(
    ! [X26,X27,X28] :
      ( ( X27 = k1_xboole_0
        | ~ r2_hidden(X27,X26)
        | k3_tarski(X26) != k1_xboole_0 )
      & ( esk4_1(X28) != k1_xboole_0
        | k3_tarski(X28) = k1_xboole_0 )
      & ( r2_hidden(esk4_1(X28),X28)
        | k3_tarski(X28) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).

fof(c_0_9,plain,(
    ! [X5,X7,X8] :
      ( ( r2_hidden(esk1_1(X5),X5)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(X7,X5)
        | esk1_1(X5) != k4_tarski(X7,X8)
        | X5 = k1_xboole_0 )
      & ( ~ r2_hidden(X8,X5)
        | esk1_1(X5) != k4_tarski(X7,X8)
        | X5 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_10,negated_conjecture,(
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

fof(c_0_11,plain,(
    ! [X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X17,X16)
        | m2_orders_2(X17,X14,X15)
        | X16 != k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ m2_orders_2(X18,X14,X15)
        | r2_hidden(X18,X16)
        | X16 != k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( ~ r2_hidden(esk3_3(X14,X15,X19),X19)
        | ~ m2_orders_2(esk3_3(X14,X15,X19),X14,X15)
        | X19 = k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk3_3(X14,X15,X19),X19)
        | m2_orders_2(esk3_3(X14,X15,X19),X14,X15)
        | X19 = k4_orders_2(X14,X15)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).

cnf(c_0_12,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | k3_tarski(X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))
    & k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_15,plain,
    ( m2_orders_2(X1,X3,X4)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k4_orders_2(X3,X4)
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( esk1_1(X1) = k1_xboole_0
    | X1 = k1_xboole_0
    | k3_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( k3_tarski(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m2_orders_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,k4_orders_2(X2,X3)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( esk1_1(k4_orders_2(esk5_0,esk6_0)) = k1_xboole_0
    | k4_orders_2(esk5_0,esk6_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_26,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X11 != k1_xboole_0
        | ~ m2_orders_2(X11,X9,X10)
        | ~ v6_orders_2(X11,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_wellord1(u1_orders_2(X9),X11)
        | ~ m2_orders_2(X11,X9,X10)
        | ~ v6_orders_2(X11,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X11)
        | k1_funct_1(X10,k1_orders_2(X9,k3_orders_2(X9,X11,X12))) = X12
        | ~ m2_orders_2(X11,X9,X10)
        | ~ v6_orders_2(X11,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk2_3(X9,X10,X11),u1_struct_0(X9))
        | X11 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X9),X11)
        | m2_orders_2(X11,X9,X10)
        | ~ v6_orders_2(X11,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk2_3(X9,X10,X11),X11)
        | X11 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X9),X11)
        | m2_orders_2(X11,X9,X10)
        | ~ v6_orders_2(X11,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) )
      & ( k1_funct_1(X10,k1_orders_2(X9,k3_orders_2(X9,X11,esk2_3(X9,X10,X11)))) != esk2_3(X9,X10,X11)
        | X11 = k1_xboole_0
        | ~ r2_wellord1(u1_orders_2(X9),X11)
        | m2_orders_2(X11,X9,X10)
        | ~ v6_orders_2(X11,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))
        | v2_struct_0(X9)
        | ~ v3_orders_2(X9)
        | ~ v4_orders_2(X9)
        | ~ v5_orders_2(X9)
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).

fof(c_0_27,plain,(
    ! [X21,X22,X23] :
      ( ( v6_orders_2(X23,X21)
        | ~ m2_orders_2(X23,X21,X22)
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(X21))) )
      & ( m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ m2_orders_2(X23,X21,X22)
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_orders_1(X22,k1_orders_1(u1_struct_0(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_28,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v3_orders_2(X24)
      | ~ v4_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_orders_1(X25,k1_orders_1(u1_struct_0(X24)))
      | ~ v1_xboole_0(k4_orders_2(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).

cnf(c_0_29,negated_conjecture,
    ( m2_orders_2(X1,esk5_0,esk6_0)
    | ~ r2_hidden(X1,k4_orders_2(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( k4_orders_2(esk5_0,esk6_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k4_orders_2(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,plain,
    ( v6_orders_2(X1,X2)
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ v1_xboole_0(k4_orders_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k4_orders_2(esk5_0,esk6_0) = k1_xboole_0
    | m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ m2_orders_2(k1_xboole_0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_32])]),c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m2_orders_2(k1_xboole_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_36])]),c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_19]),c_0_38]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:42:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.032 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t91_orders_1, axiom, ![X1]:(~((?[X2]:(X2!=k1_xboole_0&r2_hidden(X2,X1))&k3_tarski(X1)=k1_xboole_0))&~((k3_tarski(X1)!=k1_xboole_0&![X2]:~((X2!=k1_xboole_0&r2_hidden(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 0.21/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.21/0.38  fof(t87_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 0.21/0.38  fof(d17_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(X3=k4_orders_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>m2_orders_2(X4,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 0.21/0.38  fof(d16_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:((v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))=>(m2_orders_2(X3,X1,X2)<=>((X3!=k1_xboole_0&r2_wellord1(u1_orders_2(X1),X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X3)=>k1_funct_1(X2,k1_orders_2(X1,k3_orders_2(X1,X3,X4)))=X4))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_orders_2)).
% 0.21/0.38  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.21/0.38  fof(fc9_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>~(v1_xboole_0(k4_orders_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 0.21/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.38  fof(c_0_8, plain, ![X26, X27, X28]:((X27=k1_xboole_0|~r2_hidden(X27,X26)|k3_tarski(X26)!=k1_xboole_0)&((esk4_1(X28)!=k1_xboole_0|k3_tarski(X28)=k1_xboole_0)&(r2_hidden(esk4_1(X28),X28)|k3_tarski(X28)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_orders_1])])])])])])).
% 0.21/0.38  fof(c_0_9, plain, ![X5, X7, X8]:((r2_hidden(esk1_1(X5),X5)|X5=k1_xboole_0)&((~r2_hidden(X7,X5)|esk1_1(X5)!=k4_tarski(X7,X8)|X5=k1_xboole_0)&(~r2_hidden(X8,X5)|esk1_1(X5)!=k4_tarski(X7,X8)|X5=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.21/0.38  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>k3_tarski(k4_orders_2(X1,X2))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t87_orders_2])).
% 0.21/0.38  fof(c_0_11, plain, ![X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X17,X16)|m2_orders_2(X17,X14,X15)|X16!=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)))&(~m2_orders_2(X18,X14,X15)|r2_hidden(X18,X16)|X16!=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))&((~r2_hidden(esk3_3(X14,X15,X19),X19)|~m2_orders_2(esk3_3(X14,X15,X19),X14,X15)|X19=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)))&(r2_hidden(esk3_3(X14,X15,X19),X19)|m2_orders_2(esk3_3(X14,X15,X19),X14,X15)|X19=k4_orders_2(X14,X15)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_orders_2])])])])])])])).
% 0.21/0.38  cnf(c_0_12, plain, (X1=k1_xboole_0|~r2_hidden(X1,X2)|k3_tarski(X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))&k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.21/0.38  cnf(c_0_15, plain, (m2_orders_2(X1,X3,X4)|v2_struct_0(X3)|~r2_hidden(X1,X2)|X2!=k4_orders_2(X3,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))|~v3_orders_2(X3)|~v4_orders_2(X3)|~v5_orders_2(X3)|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_16, plain, (esk1_1(X1)=k1_xboole_0|X1=k1_xboole_0|k3_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.21/0.38  cnf(c_0_17, negated_conjecture, (k3_tarski(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_18, plain, (m2_orders_2(X1,X2,X3)|v2_struct_0(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~r2_hidden(X1,k4_orders_2(X2,X3))), inference(er,[status(thm)],[c_0_15])).
% 0.21/0.38  cnf(c_0_19, negated_conjecture, (m1_orders_1(esk6_0,k1_orders_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (esk1_1(k4_orders_2(esk5_0,esk6_0))=k1_xboole_0|k4_orders_2(esk5_0,esk6_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.38  fof(c_0_26, plain, ![X9, X10, X11, X12]:((((X11!=k1_xboole_0|~m2_orders_2(X11,X9,X10)|(~v6_orders_2(X11,X9)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&(r2_wellord1(u1_orders_2(X9),X11)|~m2_orders_2(X11,X9,X10)|(~v6_orders_2(X11,X9)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))&(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X11)|k1_funct_1(X10,k1_orders_2(X9,k3_orders_2(X9,X11,X12)))=X12)|~m2_orders_2(X11,X9,X10)|(~v6_orders_2(X11,X9)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9))))&((m1_subset_1(esk2_3(X9,X10,X11),u1_struct_0(X9))|(X11=k1_xboole_0|~r2_wellord1(u1_orders_2(X9),X11))|m2_orders_2(X11,X9,X10)|(~v6_orders_2(X11,X9)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&((r2_hidden(esk2_3(X9,X10,X11),X11)|(X11=k1_xboole_0|~r2_wellord1(u1_orders_2(X9),X11))|m2_orders_2(X11,X9,X10)|(~v6_orders_2(X11,X9)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))&(k1_funct_1(X10,k1_orders_2(X9,k3_orders_2(X9,X11,esk2_3(X9,X10,X11))))!=esk2_3(X9,X10,X11)|(X11=k1_xboole_0|~r2_wellord1(u1_orders_2(X9),X11))|m2_orders_2(X11,X9,X10)|(~v6_orders_2(X11,X9)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))))|~m1_orders_1(X10,k1_orders_1(u1_struct_0(X9)))|(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_orders_2])])])])])])).
% 0.21/0.38  fof(c_0_27, plain, ![X21, X22, X23]:((v6_orders_2(X23,X21)|~m2_orders_2(X23,X21,X22)|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_orders_1(X22,k1_orders_1(u1_struct_0(X21)))))&(m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21)))|~m2_orders_2(X23,X21,X22)|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_orders_1(X22,k1_orders_1(u1_struct_0(X21)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.21/0.38  fof(c_0_28, plain, ![X24, X25]:(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_orders_1(X25,k1_orders_1(u1_struct_0(X24)))|~v1_xboole_0(k4_orders_2(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_orders_2])])])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (m2_orders_2(X1,esk5_0,esk6_0)|~r2_hidden(X1,k4_orders_2(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (k4_orders_2(esk5_0,esk6_0)=k1_xboole_0|r2_hidden(k1_xboole_0,k4_orders_2(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_13, c_0_25])).
% 0.21/0.38  cnf(c_0_31, plain, (v2_struct_0(X2)|X1!=k1_xboole_0|~m2_orders_2(X1,X2,X3)|~v6_orders_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.38  cnf(c_0_32, plain, (v6_orders_2(X1,X2)|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.38  cnf(c_0_34, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~v1_xboole_0(k4_orders_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.38  cnf(c_0_35, negated_conjecture, (k4_orders_2(esk5_0,esk6_0)=k1_xboole_0|m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.38  cnf(c_0_36, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.38  cnf(c_0_37, plain, (v2_struct_0(X1)|~m2_orders_2(k1_xboole_0,X1,X2)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_32])]), c_0_33])).
% 0.21/0.38  cnf(c_0_38, negated_conjecture, (m2_orders_2(k1_xboole_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_36])]), c_0_24])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_19]), c_0_38]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 40
% 0.21/0.38  # Proof object clause steps            : 24
% 0.21/0.38  # Proof object formula steps           : 16
% 0.21/0.38  # Proof object conjectures             : 16
% 0.21/0.38  # Proof object clause conjectures      : 13
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 15
% 0.21/0.38  # Proof object initial formulas used   : 8
% 0.21/0.38  # Proof object generating inferences   : 7
% 0.21/0.38  # Proof object simplifying inferences  : 25
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 8
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 27
% 0.21/0.38  # Removed in clause preprocessing      : 0
% 0.21/0.38  # Initial clauses in saturation        : 27
% 0.21/0.38  # Processed clauses                    : 81
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 4
% 0.21/0.38  # ...remaining for further processing  : 77
% 0.21/0.38  # Other redundant clauses eliminated   : 3
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 1
% 0.21/0.38  # Generated clauses                    : 38
% 0.21/0.38  # ...of the previous two non-trivial   : 33
% 0.21/0.38  # Contextual simplify-reflections      : 6
% 0.21/0.38  # Paramodulations                      : 35
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 3
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 46
% 0.21/0.38  #    Positive orientable unit clauses  : 8
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 1
% 0.21/0.38  #    Non-unit-clauses                  : 37
% 0.21/0.38  # Current number of unprocessed clauses: 4
% 0.21/0.38  # ...number of literals in the above   : 33
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 28
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 926
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 125
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.21/0.38  # Unit Clause-clause subsumption calls : 1
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 1
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 4104
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.036 s
% 0.21/0.39  # System time              : 0.005 s
% 0.21/0.39  # Total time               : 0.041 s
% 0.21/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
