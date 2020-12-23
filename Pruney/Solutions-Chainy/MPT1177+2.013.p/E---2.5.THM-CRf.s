%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:06 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 (1120 expanded)
%              Number of clauses        :   54 ( 370 expanded)
%              Number of leaves         :   15 ( 270 expanded)
%              Depth                    :   15
%              Number of atoms          :  353 (8390 expanded)
%              Number of equality atoms :   41 ( 134 expanded)
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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t34_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4,X5,X6] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_mcart_1(X3,X4,X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

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

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(irreflexivity_r2_xboole_0,axiom,(
    ! [X1,X2] : ~ r2_xboole_0(X1,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X53,X54,X55] :
      ( ( v6_orders_2(X55,X53)
        | ~ m2_orders_2(X55,X53,X54)
        | v2_struct_0(X53)
        | ~ v3_orders_2(X53)
        | ~ v4_orders_2(X53)
        | ~ v5_orders_2(X53)
        | ~ l1_orders_2(X53)
        | ~ m1_orders_1(X54,k1_orders_1(u1_struct_0(X53))) )
      & ( m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))
        | ~ m2_orders_2(X55,X53,X54)
        | v2_struct_0(X53)
        | ~ v3_orders_2(X53)
        | ~ v4_orders_2(X53)
        | ~ v5_orders_2(X53)
        | ~ l1_orders_2(X53)
        | ~ m1_orders_1(X54,k1_orders_1(u1_struct_0(X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).

fof(c_0_17,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X56,X57,X58] :
      ( v2_struct_0(X56)
      | ~ v3_orders_2(X56)
      | ~ v4_orders_2(X56)
      | ~ v5_orders_2(X56)
      | ~ l1_orders_2(X56)
      | ~ m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))
      | ~ m1_orders_2(X58,X56,X57)
      | r1_tarski(X58,X57) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m2_orders_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | ~ r2_xboole_0(X7,X8) )
      & ( X7 != X8
        | ~ r2_xboole_0(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | X7 = X8
        | r2_xboole_0(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_29,plain,(
    ! [X42,X43] :
      ( ~ r2_hidden(X42,X43)
      | ~ r1_tarski(X43,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_30,plain,(
    ! [X44,X46,X47,X48,X49] :
      ( ( r2_hidden(esk1_1(X44),X44)
        | X44 = k1_xboole_0 )
      & ( ~ r2_hidden(X46,X44)
        | esk1_1(X44) != k4_mcart_1(X46,X47,X48,X49)
        | X44 = k1_xboole_0 )
      & ( ~ r2_hidden(X47,X44)
        | esk1_1(X44) != k4_mcart_1(X46,X47,X48,X49)
        | X44 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).

fof(c_0_31,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,k2_xboole_0(X15,X16))
      | r1_tarski(k4_xboole_0(X14,X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_32,plain,(
    ! [X20,X21] : r1_tarski(X20,k2_xboole_0(X20,X21)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_xboole_0(esk4_0,esk5_0)
    | m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_41,plain,(
    ! [X66,X67,X68,X69] :
      ( ( ~ m1_orders_2(X68,X66,X69)
        | ~ m1_orders_2(X69,X66,X68)
        | X68 = X69
        | ~ m2_orders_2(X69,X66,X67)
        | ~ m2_orders_2(X68,X66,X67)
        | ~ m1_orders_1(X67,k1_orders_1(u1_struct_0(X66)))
        | v2_struct_0(X66)
        | ~ v3_orders_2(X66)
        | ~ v4_orders_2(X66)
        | ~ v5_orders_2(X66)
        | ~ l1_orders_2(X66) )
      & ( m1_orders_2(X69,X66,X68)
        | m1_orders_2(X68,X66,X69)
        | X68 = X69
        | ~ m2_orders_2(X69,X66,X67)
        | ~ m2_orders_2(X68,X66,X67)
        | ~ m1_orders_1(X67,k1_orders_1(u1_struct_0(X66)))
        | v2_struct_0(X66)
        | ~ v3_orders_2(X66)
        | ~ v4_orders_2(X66)
        | ~ v5_orders_2(X66)
        | ~ l1_orders_2(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(X1,esk5_0)
    | ~ m1_orders_2(X1,esk2_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_43,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk5_0)
    | r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_1(X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k4_xboole_0(X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m2_orders_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( X1 = X2
    | m1_orders_2(X1,esk2_0,X2)
    | m1_orders_2(X2,esk2_0,X1)
    | ~ m2_orders_2(X2,esk2_0,esk3_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_xboole_0(esk4_0,esk5_0)
    | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = esk4_0
    | r2_xboole_0(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_54,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_49])).

fof(c_0_56,plain,(
    ! [X59,X60,X61] :
      ( v2_struct_0(X59)
      | ~ v3_orders_2(X59)
      | ~ v4_orders_2(X59)
      | ~ v5_orders_2(X59)
      | ~ l1_orders_2(X59)
      | ~ m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))
      | ~ m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))
      | X60 = k1_xboole_0
      | ~ m1_orders_2(X60,X59,X61)
      | ~ m1_orders_2(X61,X59,X60) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).

fof(c_0_57,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v3_orders_2(X50)
      | ~ v4_orders_2(X50)
      | ~ v5_orders_2(X50)
      | ~ l1_orders_2(X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))
      | ~ m1_orders_2(X52,X50,X51)
      | m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk5_0
    | m1_orders_2(esk5_0,esk2_0,X1)
    | m1_orders_2(X1,esk2_0,esk5_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ m1_orders_2(esk4_0,esk2_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_61,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_62,plain,(
    ! [X62,X63,X64,X65] :
      ( v2_struct_0(X62)
      | ~ v3_orders_2(X62)
      | ~ v4_orders_2(X62)
      | ~ v5_orders_2(X62)
      | ~ l1_orders_2(X62)
      | ~ m1_orders_1(X63,k1_orders_1(u1_struct_0(X62)))
      | ~ m2_orders_2(X64,X62,X63)
      | ~ m2_orders_2(X65,X62,X63)
      | ~ r1_xboole_0(X64,X65) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).

fof(c_0_63,plain,(
    ! [X22,X23] :
      ( ( ~ r1_xboole_0(X22,X23)
        | k4_xboole_0(X22,X23) = X22 )
      & ( k4_xboole_0(X22,X23) != X22
        | r1_xboole_0(X22,X23) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_64,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_55])).

cnf(c_0_65,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ m1_orders_2(X1,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_58]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_68,negated_conjecture,
    ( esk5_0 = esk4_0
    | m1_orders_2(esk5_0,esk2_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = esk4_0
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_48])).

fof(c_0_70,plain,(
    ! [X9] : ~ r2_xboole_0(X9,X9) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).

cnf(c_0_71,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2)
    | ~ m2_orders_2(X4,X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_73,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_64])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X3,X2,X1)
    | ~ m1_orders_2(X1,X2,X3)
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_76,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( ~ m2_orders_2(X1,esk2_0,esk3_0)
    | ~ m2_orders_2(X2,esk2_0,esk3_0)
    | ~ r1_xboole_0(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_78,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_orders_2(esk4_0,esk2_0,X1)
    | ~ m1_orders_2(X1,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_58]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( m1_orders_2(esk4_0,esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_75]),c_0_75]),c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( ~ m2_orders_2(k1_xboole_0,esk2_0,esk3_0)
    | ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k1_xboole_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_80])])).

cnf(c_0_83,negated_conjecture,
    ( ~ m2_orders_2(X1,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_50])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_50,c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:59:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.55  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.55  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.55  #
% 0.19/0.55  # Preprocessing time       : 0.030 s
% 0.19/0.55  # Presaturation interreduction done
% 0.19/0.55  
% 0.19/0.55  # Proof found!
% 0.19/0.55  # SZS status Theorem
% 0.19/0.55  # SZS output start CNFRefutation
% 0.19/0.55  fof(t84_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 0.19/0.55  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.19/0.55  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.19/0.55  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.19/0.55  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.55  fof(t34_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4, X5, X6]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_mcart_1(X3,X4,X5,X6))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 0.19/0.55  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 0.19/0.55  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.19/0.55  fof(t83_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(X3!=X4=>(m1_orders_2(X3,X1,X4)<=>~(m1_orders_2(X4,X1,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 0.19/0.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.55  fof(t69_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 0.19/0.55  fof(dt_m1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_orders_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_orders_2)).
% 0.19/0.55  fof(t82_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>~(r1_xboole_0(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_orders_2)).
% 0.19/0.55  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.19/0.55  fof(irreflexivity_r2_xboole_0, axiom, ![X1, X2]:~(r2_xboole_0(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 0.19/0.55  fof(c_0_15, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4))))))), inference(assume_negation,[status(cth)],[t84_orders_2])).
% 0.19/0.55  fof(c_0_16, plain, ![X53, X54, X55]:((v6_orders_2(X55,X53)|~m2_orders_2(X55,X53,X54)|(v2_struct_0(X53)|~v3_orders_2(X53)|~v4_orders_2(X53)|~v5_orders_2(X53)|~l1_orders_2(X53)|~m1_orders_1(X54,k1_orders_1(u1_struct_0(X53)))))&(m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X53)))|~m2_orders_2(X55,X53,X54)|(v2_struct_0(X53)|~v3_orders_2(X53)|~v4_orders_2(X53)|~v5_orders_2(X53)|~l1_orders_2(X53)|~m1_orders_1(X54,k1_orders_1(u1_struct_0(X53)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.19/0.55  fof(c_0_17, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))&(m2_orders_2(esk4_0,esk2_0,esk3_0)&(m2_orders_2(esk5_0,esk2_0,esk3_0)&((~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0))&(r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.19/0.55  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.55  cnf(c_0_19, negated_conjecture, (m1_orders_1(esk3_0,k1_orders_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_21, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_22, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  fof(c_0_25, plain, ![X56, X57, X58]:(v2_struct_0(X56)|~v3_orders_2(X56)|~v4_orders_2(X56)|~v5_orders_2(X56)|~l1_orders_2(X56)|(~m1_subset_1(X57,k1_zfmisc_1(u1_struct_0(X56)))|(~m1_orders_2(X58,X56,X57)|r1_tarski(X58,X57)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.19/0.55  cnf(c_0_26, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.55  cnf(c_0_27, negated_conjecture, (m2_orders_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  fof(c_0_28, plain, ![X7, X8]:(((r1_tarski(X7,X8)|~r2_xboole_0(X7,X8))&(X7!=X8|~r2_xboole_0(X7,X8)))&(~r1_tarski(X7,X8)|X7=X8|r2_xboole_0(X7,X8))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.19/0.55  fof(c_0_29, plain, ![X42, X43]:(~r2_hidden(X42,X43)|~r1_tarski(X43,X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.55  fof(c_0_30, plain, ![X44, X46, X47, X48, X49]:((r2_hidden(esk1_1(X44),X44)|X44=k1_xboole_0)&((~r2_hidden(X46,X44)|esk1_1(X44)!=k4_mcart_1(X46,X47,X48,X49)|X44=k1_xboole_0)&(~r2_hidden(X47,X44)|esk1_1(X44)!=k4_mcart_1(X46,X47,X48,X49)|X44=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_mcart_1])])])])])])).
% 0.19/0.55  fof(c_0_31, plain, ![X14, X15, X16]:(~r1_tarski(X14,k2_xboole_0(X15,X16))|r1_tarski(k4_xboole_0(X14,X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 0.19/0.55  fof(c_0_32, plain, ![X20, X21]:r1_tarski(X20,k2_xboole_0(X20,X21)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.19/0.55  cnf(c_0_33, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.55  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.55  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.55  cnf(c_0_36, negated_conjecture, (r2_xboole_0(esk4_0,esk5_0)|m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_37, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.55  cnf(c_0_38, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.55  cnf(c_0_39, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.55  cnf(c_0_40, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.55  fof(c_0_41, plain, ![X66, X67, X68, X69]:((~m1_orders_2(X68,X66,X69)|~m1_orders_2(X69,X66,X68)|X68=X69|~m2_orders_2(X69,X66,X67)|~m2_orders_2(X68,X66,X67)|~m1_orders_1(X67,k1_orders_1(u1_struct_0(X66)))|(v2_struct_0(X66)|~v3_orders_2(X66)|~v4_orders_2(X66)|~v5_orders_2(X66)|~l1_orders_2(X66)))&(m1_orders_2(X69,X66,X68)|m1_orders_2(X68,X66,X69)|X68=X69|~m2_orders_2(X69,X66,X67)|~m2_orders_2(X68,X66,X67)|~m1_orders_1(X67,k1_orders_1(u1_struct_0(X66)))|(v2_struct_0(X66)|~v3_orders_2(X66)|~v4_orders_2(X66)|~v5_orders_2(X66)|~l1_orders_2(X66)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).
% 0.19/0.55  cnf(c_0_42, negated_conjecture, (r1_tarski(X1,esk5_0)|~m1_orders_2(X1,esk2_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.55  cnf(c_0_43, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk5_0)|r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.55  cnf(c_0_44, plain, (X1=k1_xboole_0|~r1_tarski(X1,esk1_1(X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.55  cnf(c_0_45, plain, (r1_tarski(k4_xboole_0(X1,X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.55  cnf(c_0_46, plain, (m1_orders_2(X1,X2,X3)|m1_orders_2(X3,X2,X1)|X3=X1|v2_struct_0(X2)|~m2_orders_2(X1,X2,X4)|~m2_orders_2(X3,X2,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.55  cnf(c_0_47, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.55  cnf(c_0_48, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.19/0.55  cnf(c_0_49, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.55  cnf(c_0_50, negated_conjecture, (m2_orders_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_51, negated_conjecture, (X1=X2|m1_orders_2(X1,esk2_0,X2)|m1_orders_2(X2,esk2_0,X1)|~m2_orders_2(X2,esk2_0,esk3_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.55  cnf(c_0_52, negated_conjecture, (~r2_xboole_0(esk4_0,esk5_0)|~m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.55  cnf(c_0_53, negated_conjecture, (esk5_0=esk4_0|r2_xboole_0(esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.55  fof(c_0_54, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.55  cnf(c_0_55, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_45, c_0_49])).
% 0.19/0.55  fof(c_0_56, plain, ![X59, X60, X61]:(v2_struct_0(X59)|~v3_orders_2(X59)|~v4_orders_2(X59)|~v5_orders_2(X59)|~l1_orders_2(X59)|(~m1_subset_1(X60,k1_zfmisc_1(u1_struct_0(X59)))|(~m1_subset_1(X61,k1_zfmisc_1(u1_struct_0(X59)))|(X60=k1_xboole_0|~m1_orders_2(X60,X59,X61)|~m1_orders_2(X61,X59,X60))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).
% 0.19/0.55  fof(c_0_57, plain, ![X50, X51, X52]:(v2_struct_0(X50)|~v3_orders_2(X50)|~v4_orders_2(X50)|~v5_orders_2(X50)|~l1_orders_2(X50)|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X50)))|(~m1_orders_2(X52,X50,X51)|m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_orders_2])])])])).
% 0.19/0.55  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_26, c_0_50])).
% 0.19/0.55  cnf(c_0_59, negated_conjecture, (X1=esk5_0|m1_orders_2(esk5_0,esk2_0,X1)|m1_orders_2(X1,esk2_0,esk5_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_27])).
% 0.19/0.55  cnf(c_0_60, negated_conjecture, (esk5_0=esk4_0|~m1_orders_2(esk4_0,esk2_0,esk5_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.55  cnf(c_0_61, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.55  fof(c_0_62, plain, ![X62, X63, X64, X65]:(v2_struct_0(X62)|~v3_orders_2(X62)|~v4_orders_2(X62)|~v5_orders_2(X62)|~l1_orders_2(X62)|(~m1_orders_1(X63,k1_orders_1(u1_struct_0(X62)))|(~m2_orders_2(X64,X62,X63)|(~m2_orders_2(X65,X62,X63)|~r1_xboole_0(X64,X65))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t82_orders_2])])])])).
% 0.19/0.55  fof(c_0_63, plain, ![X22, X23]:((~r1_xboole_0(X22,X23)|k4_xboole_0(X22,X23)=X22)&(k4_xboole_0(X22,X23)!=X22|r1_xboole_0(X22,X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.19/0.55  cnf(c_0_64, plain, (r1_tarski(k4_xboole_0(k1_xboole_0,X1),X2)), inference(spm,[status(thm)],[c_0_39, c_0_55])).
% 0.19/0.55  cnf(c_0_65, plain, (v2_struct_0(X1)|X2=k1_xboole_0|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X2,X1,X3)|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.55  cnf(c_0_66, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.55  cnf(c_0_67, negated_conjecture, (r1_tarski(X1,esk4_0)|~m1_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_58]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.55  cnf(c_0_68, negated_conjecture, (esk5_0=esk4_0|m1_orders_2(esk5_0,esk2_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_50]), c_0_60])).
% 0.19/0.55  cnf(c_0_69, negated_conjecture, (esk5_0=esk4_0|~r1_tarski(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_61, c_0_48])).
% 0.19/0.55  fof(c_0_70, plain, ![X9]:~r2_xboole_0(X9,X9), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_xboole_0])])).
% 0.19/0.55  cnf(c_0_71, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)|~m2_orders_2(X4,X1,X2)|~r1_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.55  cnf(c_0_72, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.55  cnf(c_0_73, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_64])).
% 0.19/0.55  cnf(c_0_74, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X3,X2,X1)|~m1_orders_2(X1,X2,X3)|~l1_orders_2(X2)|~v5_orders_2(X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.55  cnf(c_0_75, negated_conjecture, (esk5_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.19/0.55  cnf(c_0_76, plain, (~r2_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.19/0.55  cnf(c_0_77, negated_conjecture, (~m2_orders_2(X1,esk2_0,esk3_0)|~m2_orders_2(X2,esk2_0,esk3_0)|~r1_xboole_0(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.55  cnf(c_0_78, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.55  cnf(c_0_79, negated_conjecture, (X1=k1_xboole_0|~m1_orders_2(esk4_0,esk2_0,X1)|~m1_orders_2(X1,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_58]), c_0_20]), c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.19/0.55  cnf(c_0_80, negated_conjecture, (m1_orders_2(esk4_0,esk2_0,esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_75]), c_0_75]), c_0_76])).
% 0.19/0.55  cnf(c_0_81, negated_conjecture, (~m2_orders_2(k1_xboole_0,esk2_0,esk3_0)|~m2_orders_2(X1,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.55  cnf(c_0_82, negated_conjecture, (k1_xboole_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_80])])).
% 0.19/0.55  cnf(c_0_83, negated_conjecture, (~m2_orders_2(X1,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_50])])).
% 0.19/0.55  cnf(c_0_84, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_50, c_0_83]), ['proof']).
% 0.19/0.55  # SZS output end CNFRefutation
% 0.19/0.55  # Proof object total steps             : 85
% 0.19/0.55  # Proof object clause steps            : 54
% 0.19/0.55  # Proof object formula steps           : 31
% 0.19/0.55  # Proof object conjectures             : 34
% 0.19/0.55  # Proof object clause conjectures      : 31
% 0.19/0.55  # Proof object formula conjectures     : 3
% 0.19/0.55  # Proof object initial clauses used    : 25
% 0.19/0.55  # Proof object initial formulas used   : 15
% 0.19/0.55  # Proof object generating inferences   : 24
% 0.19/0.55  # Proof object simplifying inferences  : 49
% 0.19/0.55  # Training examples: 0 positive, 0 negative
% 0.19/0.55  # Parsed axioms                        : 28
% 0.19/0.55  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.55  # Initial clauses                      : 48
% 0.19/0.55  # Removed in clause preprocessing      : 2
% 0.19/0.55  # Initial clauses in saturation        : 46
% 0.19/0.55  # Processed clauses                    : 1550
% 0.19/0.55  # ...of these trivial                  : 43
% 0.19/0.55  # ...subsumed                          : 616
% 0.19/0.55  # ...remaining for further processing  : 891
% 0.19/0.55  # Other redundant clauses eliminated   : 74
% 0.19/0.55  # Clauses deleted for lack of memory   : 0
% 0.19/0.55  # Backward-subsumed                    : 16
% 0.19/0.55  # Backward-rewritten                   : 472
% 0.19/0.55  # Generated clauses                    : 9566
% 0.19/0.55  # ...of the previous two non-trivial   : 7989
% 0.19/0.55  # Contextual simplify-reflections      : 5
% 0.19/0.55  # Paramodulations                      : 9489
% 0.19/0.55  # Factorizations                       : 2
% 0.19/0.55  # Equation resolutions                 : 74
% 0.19/0.55  # Propositional unsat checks           : 0
% 0.19/0.55  #    Propositional check models        : 0
% 0.19/0.55  #    Propositional check unsatisfiable : 0
% 0.19/0.55  #    Propositional clauses             : 0
% 0.19/0.55  #    Propositional clauses after purity: 0
% 0.19/0.55  #    Propositional unsat core size     : 0
% 0.19/0.55  #    Propositional preprocessing time  : 0.000
% 0.19/0.55  #    Propositional encoding time       : 0.000
% 0.19/0.55  #    Propositional solver time         : 0.000
% 0.19/0.55  #    Success case prop preproc time    : 0.000
% 0.19/0.55  #    Success case prop encoding time   : 0.000
% 0.19/0.55  #    Success case prop solver time     : 0.000
% 0.19/0.55  # Current number of processed clauses  : 355
% 0.19/0.55  #    Positive orientable unit clauses  : 48
% 0.19/0.55  #    Positive unorientable unit clauses: 0
% 0.19/0.55  #    Negative unit clauses             : 74
% 0.19/0.55  #    Non-unit-clauses                  : 233
% 0.19/0.55  # Current number of unprocessed clauses: 6394
% 0.19/0.55  # ...number of literals in the above   : 22064
% 0.19/0.55  # Current number of archived formulas  : 0
% 0.19/0.55  # Current number of archived clauses   : 535
% 0.19/0.55  # Clause-clause subsumption calls (NU) : 34946
% 0.19/0.55  # Rec. Clause-clause subsumption calls : 19762
% 0.19/0.55  # Non-unit clause-clause subsumptions  : 247
% 0.19/0.55  # Unit Clause-clause subsumption calls : 1942
% 0.19/0.55  # Rewrite failures with RHS unbound    : 0
% 0.19/0.55  # BW rewrite match attempts            : 52
% 0.19/0.55  # BW rewrite match successes           : 24
% 0.19/0.55  # Condensation attempts                : 0
% 0.19/0.55  # Condensation successes               : 0
% 0.19/0.55  # Termbank termtop insertions          : 130393
% 0.19/0.55  
% 0.19/0.55  # -------------------------------------------------
% 0.19/0.55  # User time                : 0.209 s
% 0.19/0.55  # System time              : 0.012 s
% 0.19/0.55  # Total time               : 0.221 s
% 0.19/0.55  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
