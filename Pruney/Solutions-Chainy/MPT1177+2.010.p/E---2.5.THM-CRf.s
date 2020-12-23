%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:06 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 614 expanded)
%              Number of clauses        :   50 ( 204 expanded)
%              Number of leaves         :   11 ( 148 expanded)
%              Depth                    :   14
%              Number of atoms          :  306 (4575 expanded)
%              Number of equality atoms :   34 (  76 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   2 average)
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

fof(t79_orders_2,axiom,(
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
             => r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t61_xboole_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => r2_xboole_0(k1_xboole_0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(t68_orders_2,axiom,(
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

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
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

fof(c_0_13,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
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

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_23,negated_conjecture,
    ( m2_orders_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | ~ r2_xboole_0(X11,X12) )
      & ( X11 != X12
        | ~ r2_xboole_0(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | X11 = X12
        | r2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk5_0)
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ m1_orders_2(X31,X29,X32)
        | ~ m1_orders_2(X32,X29,X31)
        | X31 = X32
        | ~ m2_orders_2(X32,X29,X30)
        | ~ m2_orders_2(X31,X29,X30)
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( m1_orders_2(X32,X29,X31)
        | m1_orders_2(X31,X29,X32)
        | X31 = X32
        | ~ m2_orders_2(X32,X29,X30)
        | ~ m2_orders_2(X31,X29,X30)
        | ~ m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ v4_orders_2(X29)
        | ~ v5_orders_2(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ m1_orders_2(X1,esk2_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

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
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( m2_orders_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( X1 = X2
    | m1_orders_2(X1,esk2_0,X2)
    | m1_orders_2(X2,esk2_0,X1)
    | ~ m2_orders_2(X2,esk2_0,esk3_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,esk5_0)
    | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_39,plain,(
    ! [X13,X14] :
      ( ( r1_tarski(X13,X14)
        | X13 != X14 )
      & ( r1_tarski(X14,X13)
        | X13 != X14 )
      & ( ~ r1_tarski(X13,X14)
        | ~ r1_tarski(X14,X13)
        | X13 = X14 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_40,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v3_orders_2(X26)
      | ~ v4_orders_2(X26)
      | ~ v5_orders_2(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))
      | ~ m2_orders_2(X28,X26,X27)
      | r2_hidden(k1_funct_1(X27,u1_struct_0(X26)),X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( X1 = esk5_0
    | m1_orders_2(esk5_0,esk2_0,X1)
    | m1_orders_2(X1,esk2_0,esk5_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_43,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_45,plain,(
    ! [X16,X17] :
      ( ~ r2_hidden(X16,X17)
      | ~ r1_tarski(X17,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_46,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_47,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_xboole_0(k1_xboole_0,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X24,X25] :
      ( ( X25 = k1_xboole_0
        | ~ m1_orders_2(X25,X24,X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) )
      & ( m1_orders_2(X25,X24,X25)
        | X25 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_orders_2])])])])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ m1_orders_2(X1,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_41]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk5_0,esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_35]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_34])).

cnf(c_0_53,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,plain,
    ( X1 = k1_xboole_0
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),X1)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_58,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk1_2(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_56])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_orders_2(esk4_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20])).

cnf(c_0_66,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_59]),c_0_59]),c_0_60])).

cnf(c_0_67,plain,
    ( esk1_2(k1_xboole_0,X1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_funct_1(esk3_0,u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_67]),c_0_68])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.34  # Version: 2.5pre002
% 0.20/0.35  # No SInE strategy applied
% 0.20/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2S
% 0.20/0.38  # and selection function SelectNewComplexAHP.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.030 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t84_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 0.20/0.38  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.20/0.38  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.20/0.38  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.38  fof(t83_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(X3!=X4=>(m1_orders_2(X3,X1,X4)<=>~(m1_orders_2(X4,X1,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 0.20/0.38  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t61_xboole_1, axiom, ![X1]:(X1!=k1_xboole_0=>r2_xboole_0(k1_xboole_0,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_xboole_1)).
% 0.20/0.38  fof(t68_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k1_xboole_0&m1_orders_2(X2,X1,X2)))&~((~(m1_orders_2(X2,X1,X2))&X2=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_orders_2)).
% 0.20/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4))))))), inference(assume_negation,[status(cth)],[t84_orders_2])).
% 0.20/0.38  fof(c_0_12, plain, ![X18, X19, X20]:((v6_orders_2(X20,X18)|~m2_orders_2(X20,X18,X19)|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_orders_1(X19,k1_orders_1(u1_struct_0(X18)))))&(m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|~m2_orders_2(X20,X18,X19)|(v2_struct_0(X18)|~v3_orders_2(X18)|~v4_orders_2(X18)|~v5_orders_2(X18)|~l1_orders_2(X18)|~m1_orders_1(X19,k1_orders_1(u1_struct_0(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk4_0,esk2_0,esk3_0)&(m2_orders_2(esk5_0,esk2_0,esk3_0)&((~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0))&(r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.20/0.38  cnf(c_0_14, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_21, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~m1_orders_2(X23,X21,X22)|r1_tarski(X23,X22)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_24, plain, ![X11, X12]:(((r1_tarski(X11,X12)|~r2_xboole_0(X11,X12))&(X11!=X12|~r2_xboole_0(X11,X12)))&(~r1_tarski(X11,X12)|X11=X12|r2_xboole_0(X11,X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.38  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  fof(c_0_29, plain, ![X29, X30, X31, X32]:((~m1_orders_2(X31,X29,X32)|~m1_orders_2(X32,X29,X31)|X31=X32|~m2_orders_2(X32,X29,X30)|~m2_orders_2(X31,X29,X30)|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)))&(m1_orders_2(X32,X29,X31)|m1_orders_2(X31,X29,X32)|X31=X32|~m2_orders_2(X32,X29,X30)|~m2_orders_2(X31,X29,X30)|~m1_orders_1(X30,k1_orders_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v3_orders_2(X29)|~v4_orders_2(X29)|~v5_orders_2(X29)|~l1_orders_2(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,esk5_0)|~m1_orders_2(X1,esk2_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_32, plain, (m1_orders_2(X1,X2,X3)|m1_orders_2(X3,X2,X1)|X3=X1|v2_struct_0(X2)|~m2_orders_2(X1,X2,X4)|~m2_orders_2(X3,X2,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_33, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.38  cnf(c_0_35, negated_conjecture, (m2_orders_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (X1=X2|m1_orders_2(X1,esk2_0,X2)|m1_orders_2(X2,esk2_0,X1)|~m2_orders_2(X2,esk2_0,esk3_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_38, negated_conjecture, (esk5_0=esk4_0|r2_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.38  fof(c_0_39, plain, ![X13, X14]:(((r1_tarski(X13,X14)|X13!=X14)&(r1_tarski(X14,X13)|X13!=X14))&(~r1_tarski(X13,X14)|~r1_tarski(X14,X13)|X13=X14)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  fof(c_0_40, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v3_orders_2(X26)|~v4_orders_2(X26)|~v5_orders_2(X26)|~l1_orders_2(X26)|(~m1_orders_1(X27,k1_orders_1(u1_struct_0(X26)))|(~m2_orders_2(X28,X26,X27)|r2_hidden(k1_funct_1(X27,u1_struct_0(X26)),X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.20/0.38  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (X1=esk5_0|m1_orders_2(esk5_0,esk2_0,X1)|m1_orders_2(X1,esk2_0,esk5_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_23])).
% 0.20/0.38  cnf(c_0_43, negated_conjecture, (esk5_0=esk4_0|~m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.38  cnf(c_0_44, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  fof(c_0_45, plain, ![X16, X17]:(~r2_hidden(X16,X17)|~r1_tarski(X17,X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.38  fof(c_0_46, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  fof(c_0_47, plain, ![X15]:(X15=k1_xboole_0|r2_xboole_0(k1_xboole_0,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_xboole_1])])).
% 0.20/0.38  cnf(c_0_48, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.38  fof(c_0_49, plain, ![X24, X25]:((X25=k1_xboole_0|~m1_orders_2(X25,X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)))&(m1_orders_2(X25,X24,X25)|X25!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_orders_2])])])])])).
% 0.20/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,esk4_0)|~m1_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_41]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk5_0,esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_35]), c_0_43])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (esk5_0=esk4_0|~r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_34])).
% 0.20/0.38  cnf(c_0_53, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.38  cnf(c_0_54, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.38  cnf(c_0_55, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.38  cnf(c_0_56, plain, (X1=k1_xboole_0|r2_xboole_0(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.38  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),X1)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_58, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.38  cnf(c_0_59, negated_conjecture, (esk5_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.20/0.38  cnf(c_0_60, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_53])).
% 0.20/0.38  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,esk1_2(X1,X2))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.38  cnf(c_0_62, plain, (X1=k1_xboole_0|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_56])).
% 0.20/0.38  cnf(c_0_63, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.38  cnf(c_0_64, negated_conjecture, (r2_hidden(k1_funct_1(esk3_0,u1_struct_0(esk2_0)),esk4_0)), inference(spm,[status(thm)],[c_0_57, c_0_35])).
% 0.20/0.38  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|~m1_orders_2(esk4_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20])).
% 0.20/0.38  cnf(c_0_66, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_59]), c_0_59]), c_0_60])).
% 0.20/0.38  cnf(c_0_67, plain, (esk1_2(k1_xboole_0,X1)=k1_xboole_0|r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.38  cnf(c_0_68, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_63])).
% 0.20/0.38  cnf(c_0_69, negated_conjecture, (~r1_tarski(esk4_0,k1_funct_1(esk3_0,u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_54, c_0_64])).
% 0.20/0.38  cnf(c_0_70, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.20/0.38  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_67]), c_0_68])])).
% 0.20/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_71])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 73
% 0.20/0.38  # Proof object clause steps            : 50
% 0.20/0.38  # Proof object formula steps           : 23
% 0.20/0.38  # Proof object conjectures             : 34
% 0.20/0.38  # Proof object clause conjectures      : 31
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 23
% 0.20/0.38  # Proof object initial formulas used   : 11
% 0.20/0.38  # Proof object generating inferences   : 22
% 0.20/0.38  # Proof object simplifying inferences  : 50
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 11
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 29
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 29
% 0.20/0.38  # Processed clauses                    : 101
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 4
% 0.20/0.38  # ...remaining for further processing  : 96
% 0.20/0.38  # Other redundant clauses eliminated   : 4
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 29
% 0.20/0.38  # Generated clauses                    : 55
% 0.20/0.38  # ...of the previous two non-trivial   : 56
% 0.20/0.38  # Contextual simplify-reflections      : 2
% 0.20/0.38  # Paramodulations                      : 51
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
% 0.20/0.38  # Current number of processed clauses  : 34
% 0.20/0.38  #    Positive orientable unit clauses  : 8
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 2
% 0.20/0.38  #    Non-unit-clauses                  : 24
% 0.20/0.38  # Current number of unprocessed clauses: 7
% 0.20/0.38  # ...number of literals in the above   : 17
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 58
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 398
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 62
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.38  # Unit Clause-clause subsumption calls : 35
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 10
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 3835
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.035 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.039 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
