%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:09 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 (2421 expanded)
%              Number of clauses        :   49 ( 749 expanded)
%              Number of leaves         :   13 ( 598 expanded)
%              Depth                    :   11
%              Number of atoms          :  332 (18961 expanded)
%              Number of equality atoms :   28 ( 345 expanded)
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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X36,X37,X38,X39] :
      ( ( ~ m1_orders_2(X38,X36,X39)
        | ~ m1_orders_2(X39,X36,X38)
        | X38 = X39
        | ~ m2_orders_2(X39,X36,X37)
        | ~ m2_orders_2(X38,X36,X37)
        | ~ m1_orders_1(X37,k1_orders_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36) )
      & ( m1_orders_2(X39,X36,X38)
        | m1_orders_2(X38,X36,X39)
        | X38 = X39
        | ~ m2_orders_2(X39,X36,X37)
        | ~ m2_orders_2(X38,X36,X37)
        | ~ m1_orders_1(X37,k1_orders_1(u1_struct_0(X36)))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v4_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m2_orders_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X23,X24,X25] :
      ( ( v6_orders_2(X25,X23)
        | ~ m2_orders_2(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23))) )
      & ( m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m2_orders_2(X25,X23,X24)
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_26,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk5_0)
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_29,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_orders_2(X28,X26,X27)
      | r1_tarski(X28,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk5_0
    | m1_orders_2(X1,esk2_0,esk5_0)
    | m1_orders_2(esk5_0,esk2_0,X1)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( m2_orders_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk5_0,esk2_0,esk4_0)
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_31]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk4_0,esk2_0,esk5_0)
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_xboole_0(X7,X8) )
      & ( r2_hidden(esk1_2(X7,X8),X8)
        | r1_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X12,X10)
        | ~ r2_hidden(X12,X11)
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_40,plain,(
    ! [X18,X19] : r1_xboole_0(k4_xboole_0(X18,X19),X19) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_41,plain,(
    ! [X15] : r1_tarski(k1_xboole_0,X15) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_42,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,esk5_0)
    | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_48,plain,(
    ! [X16,X17] : r1_tarski(k4_xboole_0(X16,X17),X16) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

fof(c_0_49,plain,(
    ! [X32,X33,X34,X35] :
      ( v2_struct_0(X32)
      | ~ v3_orders_2(X32)
      | ~ v4_orders_2(X32)
      | ~ v5_orders_2(X32)
      | ~ l1_orders_2(X32)
      | ~ m1_orders_1(X33,k1_orders_1(u1_struct_0(X32)))
      | ~ m2_orders_2(X34,X32,X33)
      | ~ m2_orders_2(X35,X32,X33)
      | ~ r1_xboole_0(X34,X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).

fof(c_0_50,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v3_orders_2(X29)
      | ~ v4_orders_2(X29)
      | ~ v5_orders_2(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))
      | X30 = k1_xboole_0
      | ~ m1_orders_2(X30,X29,X31)
      | ~ m1_orders_2(X31,X29,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).

fof(c_0_51,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v3_orders_2(X20)
      | ~ v4_orders_2(X20)
      | ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m1_orders_2(X22,X20,X21)
      | m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

cnf(c_0_52,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = esk4_0
    | r1_tarski(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_42]),c_0_43]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_54,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ r2_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_55,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_57,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_47])).

cnf(c_0_59,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_61,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])).

cnf(c_0_64,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( ~ m2_orders_2(X1,esk2_0,esk3_0)
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_31]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_63]),c_0_63]),c_0_64])).

cnf(c_0_70,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_69]),c_0_37]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_74,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73]),c_0_73]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n010.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:35:29 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S2q
% 0.21/0.40  # and selection function SelectCQArNTNp.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.029 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t84_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 0.21/0.40  fof(t83_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(X3!=X4=>(m1_orders_2(X3,X1,X4)<=>~(m1_orders_2(X4,X1,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 0.21/0.40  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.21/0.40  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.21/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.40  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.21/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.40  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.21/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.40  fof(t82_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>~(r1_xboole_0(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 0.21/0.40  fof(t69_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 0.21/0.40  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 0.21/0.40  fof(c_0_13, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4))))))), inference(assume_negation,[status(cth)],[t84_orders_2])).
% 0.21/0.40  fof(c_0_14, plain, ![X36, X37, X38, X39]:((~m1_orders_2(X38,X36,X39)|~m1_orders_2(X39,X36,X38)|X38=X39|~m2_orders_2(X39,X36,X37)|~m2_orders_2(X38,X36,X37)|~m1_orders_1(X37,k1_orders_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)))&(m1_orders_2(X39,X36,X38)|m1_orders_2(X38,X36,X39)|X38=X39|~m2_orders_2(X39,X36,X37)|~m2_orders_2(X38,X36,X37)|~m1_orders_1(X37,k1_orders_1(u1_struct_0(X36)))|(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).
% 0.21/0.40  fof(c_0_15, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk4_0,esk2_0,esk3_0)&(m2_orders_2(esk5_0,esk2_0,esk3_0)&((~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0))&(r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.21/0.40  fof(c_0_16, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.21/0.40  cnf(c_0_17, plain, (m1_orders_2(X1,X2,X3)|m1_orders_2(X3,X2,X1)|X3=X1|v2_struct_0(X2)|~m2_orders_2(X1,X2,X4)|~m2_orders_2(X3,X2,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_19, negated_conjecture, (m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_21, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  fof(c_0_25, plain, ![X23, X24, X25]:((v6_orders_2(X25,X23)|~m2_orders_2(X25,X23,X24)|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))))&(m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))|~m2_orders_2(X25,X23,X24)|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.21/0.40  fof(c_0_26, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.40  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  fof(c_0_29, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_orders_2(X28,X26,X27)|r1_tarski(X28,X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (X1=esk5_0|m1_orders_2(X1,esk2_0,esk5_0)|m1_orders_2(esk5_0,esk2_0,X1)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (m2_orders_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.40  cnf(c_0_33, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.40  cnf(c_0_35, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk5_0,esk2_0,esk4_0)|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.21/0.40  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_31]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.40  cnf(c_0_38, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk4_0,esk2_0,esk5_0)|~r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.21/0.40  fof(c_0_39, plain, ![X7, X8, X10, X11, X12]:(((r2_hidden(esk1_2(X7,X8),X7)|r1_xboole_0(X7,X8))&(r2_hidden(esk1_2(X7,X8),X8)|r1_xboole_0(X7,X8)))&(~r2_hidden(X12,X10)|~r2_hidden(X12,X11)|~r1_xboole_0(X10,X11))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.40  fof(c_0_40, plain, ![X18, X19]:r1_xboole_0(k4_xboole_0(X18,X19),X19), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.21/0.40  fof(c_0_41, plain, ![X15]:r1_tarski(k1_xboole_0,X15), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_38])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_45, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_46, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.40  cnf(c_0_47, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.40  fof(c_0_48, plain, ![X16, X17]:r1_tarski(k4_xboole_0(X16,X17),X16), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.40  fof(c_0_49, plain, ![X32, X33, X34, X35]:(v2_struct_0(X32)|~v3_orders_2(X32)|~v4_orders_2(X32)|~v5_orders_2(X32)|~l1_orders_2(X32)|(~m1_orders_1(X33,k1_orders_1(u1_struct_0(X32)))|(~m2_orders_2(X34,X32,X33)|(~m2_orders_2(X35,X32,X33)|~r1_xboole_0(X34,X35))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).
% 0.21/0.40  fof(c_0_50, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X29)))|(X30=k1_xboole_0|~m1_orders_2(X30,X29,X31)|~m1_orders_2(X31,X29,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).
% 0.21/0.40  fof(c_0_51, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_orders_2(X22,X20,X21)|m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 0.21/0.40  cnf(c_0_52, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_53, negated_conjecture, (esk5_0=esk4_0|r1_tarski(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_42]), c_0_43]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.40  cnf(c_0_54, negated_conjecture, (esk5_0=esk4_0|~r2_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.21/0.40  cnf(c_0_55, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_56, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.21/0.40  cnf(c_0_57, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_58, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_33, c_0_47])).
% 0.21/0.40  cnf(c_0_59, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.40  cnf(c_0_60, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)|~m2_orders_2(X4,X1,X2)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.40  cnf(c_0_61, plain, (v2_struct_0(X1)|X2=k1_xboole_0|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X2,X1,X3)|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.40  cnf(c_0_62, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.21/0.40  cnf(c_0_63, negated_conjecture, (esk5_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])).
% 0.21/0.40  cnf(c_0_64, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.21/0.40  cnf(c_0_65, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.40  cnf(c_0_66, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.21/0.40  cnf(c_0_67, negated_conjecture, (~m2_orders_2(X1,esk2_0,esk3_0)|~r1_xboole_0(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_31]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.40  cnf(c_0_68, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X3,X2,X1)|~m1_orders_2(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 0.21/0.40  cnf(c_0_69, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_63]), c_0_63]), c_0_64])).
% 0.21/0.40  cnf(c_0_70, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.40  cnf(c_0_71, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.21/0.40  cnf(c_0_72, negated_conjecture, (~r1_xboole_0(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_67, c_0_31])).
% 0.21/0.40  cnf(c_0_73, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_69]), c_0_37]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.21/0.40  cnf(c_0_74, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.21/0.40  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73]), c_0_73]), c_0_74])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 76
% 0.21/0.40  # Proof object clause steps            : 49
% 0.21/0.40  # Proof object formula steps           : 27
% 0.21/0.40  # Proof object conjectures             : 28
% 0.21/0.40  # Proof object clause conjectures      : 25
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 26
% 0.21/0.40  # Proof object initial formulas used   : 13
% 0.21/0.40  # Proof object generating inferences   : 19
% 0.21/0.40  # Proof object simplifying inferences  : 61
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 13
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 30
% 0.21/0.40  # Removed in clause preprocessing      : 0
% 0.21/0.40  # Initial clauses in saturation        : 30
% 0.21/0.40  # Processed clauses                    : 103
% 0.21/0.40  # ...of these trivial                  : 1
% 0.21/0.40  # ...subsumed                          : 7
% 0.21/0.40  # ...remaining for further processing  : 95
% 0.21/0.40  # Other redundant clauses eliminated   : 3
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 2
% 0.21/0.40  # Backward-rewritten                   : 22
% 0.21/0.40  # Generated clauses                    : 59
% 0.21/0.40  # ...of the previous two non-trivial   : 56
% 0.21/0.40  # Contextual simplify-reflections      : 3
% 0.21/0.40  # Paramodulations                      : 56
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 3
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 39
% 0.21/0.40  #    Positive orientable unit clauses  : 14
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 2
% 0.21/0.40  #    Non-unit-clauses                  : 23
% 0.21/0.40  # Current number of unprocessed clauses: 8
% 0.21/0.40  # ...number of literals in the above   : 21
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 53
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 712
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 90
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 11
% 0.21/0.40  # Unit Clause-clause subsumption calls : 36
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 5
% 0.21/0.40  # BW rewrite match successes           : 2
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 4339
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.033 s
% 0.21/0.40  # System time              : 0.005 s
% 0.21/0.40  # Total time               : 0.038 s
% 0.21/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
