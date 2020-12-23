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
% DateTime   : Thu Dec  3 11:10:10 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   73 (1335 expanded)
%              Number of clauses        :   49 ( 430 expanded)
%              Number of leaves         :   12 ( 323 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 (10380 expanded)
%              Number of equality atoms :   30 ( 183 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

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

fof(t78_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
         => m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X14,X15,X16] :
      ( ( v6_orders_2(X16,X14)
        | ~ m2_orders_2(X16,X14,X15)
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14))) )
      & ( m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m2_orders_2(X16,X14,X15)
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ v4_orders_2(X14)
        | ~ v5_orders_2(X14)
        | ~ l1_orders_2(X14)
        | ~ m1_orders_1(X15,k1_orders_1(u1_struct_0(X14))) ) ) ),
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

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | ~ r2_xboole_0(X5,X6) )
      & ( X5 != X6
        | ~ r2_xboole_0(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | X5 = X6
        | r2_xboole_0(X5,X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ m2_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ m1_orders_2(X30,X28,X31)
        | ~ m1_orders_2(X31,X28,X30)
        | X30 = X31
        | ~ m2_orders_2(X31,X28,X29)
        | ~ m2_orders_2(X30,X28,X29)
        | ~ m1_orders_1(X29,k1_orders_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v3_orders_2(X28)
        | ~ v4_orders_2(X28)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( m1_orders_2(X31,X28,X30)
        | m1_orders_2(X30,X28,X31)
        | X30 = X31
        | ~ m2_orders_2(X31,X28,X29)
        | ~ m2_orders_2(X30,X28,X29)
        | ~ m1_orders_1(X29,k1_orders_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v3_orders_2(X28)
        | ~ v4_orders_2(X28)
        | ~ v5_orders_2(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).

fof(c_0_25,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( r2_xboole_0(esk3_0,esk4_0)
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

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
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk4_0)
    | r1_tarski(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ m1_orders_2(X1,esk1_0,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( X1 = X2
    | m1_orders_2(X1,esk1_0,X2)
    | m1_orders_2(X2,esk1_0,X1)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m2_orders_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( esk4_0 = esk3_0
    | m1_orders_2(esk3_0,esk1_0,esk4_0)
    | ~ r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m2_orders_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_39,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | ~ v1_xboole_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_40,plain,(
    ! [X9,X10] :
      ( ~ r2_hidden(X9,X10)
      | m1_subset_1(k1_tarski(X9),k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_41,plain,(
    ! [X25,X26,X27] :
      ( v2_struct_0(X25)
      | ~ v3_orders_2(X25)
      | ~ v4_orders_2(X25)
      | ~ v5_orders_2(X25)
      | ~ l1_orders_2(X25)
      | ~ m1_orders_1(X26,k1_orders_1(u1_struct_0(X25)))
      | ~ m2_orders_2(X27,X25,X26)
      | r2_hidden(k1_funct_1(X26,u1_struct_0(X25)),X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).

fof(c_0_42,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v3_orders_2(X20)
      | ~ v4_orders_2(X20)
      | ~ v5_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
      | X21 = k1_xboole_0
      | ~ m1_orders_2(X21,X20,X22)
      | ~ m1_orders_2(X22,X20,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).

cnf(c_0_43,negated_conjecture,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ m1_orders_2(X1,esk1_0,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( X1 = esk4_0
    | m1_orders_2(esk4_0,esk1_0,X1)
    | m1_orders_2(X1,esk1_0,esk4_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = esk3_0
    | m1_orders_2(esk3_0,esk1_0,esk4_0)
    | ~ m1_orders_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_38])])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m2_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_49,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v3_orders_2(X23)
      | ~ v4_orders_2(X23)
      | ~ v5_orders_2(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))
      | m2_orders_2(k1_tarski(k1_funct_1(X24,u1_struct_0(X23))),X23,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_orders_2])])])])).

cnf(c_0_50,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( X1 = esk4_0
    | r2_xboole_0(X1,esk4_0)
    | ~ m1_orders_2(X1,esk1_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 = esk3_0
    | m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_45])).

cnf(c_0_53,plain,
    ( ~ r2_hidden(X1,k1_tarski(X2))
    | ~ r2_hidden(X2,X3)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk2_0,u1_struct_0(esk1_0)),X1)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_orders_2(X2,esk1_0,X1)
    | ~ m1_orders_2(X1,esk1_0,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_29]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_xboole_0(esk3_0,esk4_0)
    | ~ m1_orders_2(esk3_0,esk1_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( esk4_0 = esk3_0
    | r2_xboole_0(esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( ~ m2_orders_2(k1_tarski(X1),esk1_0,esk2_0)
    | ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( m2_orders_2(k1_tarski(k1_funct_1(esk2_0,u1_struct_0(esk1_0))),esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_orders_2(X2,esk1_0,X1)
    | ~ m1_orders_2(X1,esk1_0,X2)
    | ~ m2_orders_2(X2,esk1_0,esk2_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_29])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_52])).

cnf(c_0_64,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk2_0,u1_struct_0(esk1_0)),X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_orders_2(esk3_0,esk1_0,X1)
    | ~ m1_orders_2(X1,esk1_0,esk3_0)
    | ~ m2_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_38])).

cnf(c_0_67,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_63]),c_0_63]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( ~ m2_orders_2(X1,esk1_0,esk2_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_54])).

cnf(c_0_69,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_70,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_67]),c_0_38])])).

cnf(c_0_71,negated_conjecture,
    ( ~ m2_orders_2(k1_xboole_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_70]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:49:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.37  # No SInE strategy applied
% 0.15/0.37  # Trying AutoSched0 for 299 seconds
% 0.15/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.15/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.15/0.39  #
% 0.15/0.39  # Preprocessing time       : 0.022 s
% 0.15/0.39  # Presaturation interreduction done
% 0.15/0.39  
% 0.15/0.39  # Proof found!
% 0.15/0.39  # SZS status Theorem
% 0.15/0.39  # SZS output start CNFRefutation
% 0.15/0.39  fof(t84_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_orders_2)).
% 0.15/0.39  fof(dt_m2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))))=>![X3]:(m2_orders_2(X3,X1,X2)=>(v6_orders_2(X3,X1)&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_orders_2)).
% 0.15/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.15/0.39  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_orders_2)).
% 0.15/0.39  fof(t83_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(X3!=X4=>(m1_orders_2(X3,X1,X4)<=>~(m1_orders_2(X4,X1,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_orders_2)).
% 0.15/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.15/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.15/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.15/0.39  fof(t79_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 0.15/0.39  fof(t69_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 0.15/0.39  fof(t78_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_orders_2)).
% 0.15/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.15/0.39  fof(c_0_12, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))=>![X3]:(m2_orders_2(X3,X1,X2)=>![X4]:(m2_orders_2(X4,X1,X2)=>(r2_xboole_0(X3,X4)<=>m1_orders_2(X3,X1,X4))))))), inference(assume_negation,[status(cth)],[t84_orders_2])).
% 0.15/0.39  fof(c_0_13, plain, ![X14, X15, X16]:((v6_orders_2(X16,X14)|~m2_orders_2(X16,X14,X15)|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))))&(m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~m2_orders_2(X16,X14,X15)|(v2_struct_0(X14)|~v3_orders_2(X14)|~v4_orders_2(X14)|~v5_orders_2(X14)|~l1_orders_2(X14)|~m1_orders_1(X15,k1_orders_1(u1_struct_0(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m2_orders_2])])])])])).
% 0.15/0.39  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v4_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))&(m2_orders_2(esk3_0,esk1_0,esk2_0)&(m2_orders_2(esk4_0,esk1_0,esk2_0)&((~r2_xboole_0(esk3_0,esk4_0)|~m1_orders_2(esk3_0,esk1_0,esk4_0))&(r2_xboole_0(esk3_0,esk4_0)|m1_orders_2(esk3_0,esk1_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.15/0.39  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|~r2_xboole_0(X5,X6))&(X5!=X6|~r2_xboole_0(X5,X6)))&(~r1_tarski(X5,X6)|X5=X6|r2_xboole_0(X5,X6))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.15/0.39  fof(c_0_16, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(~m1_orders_2(X19,X17,X18)|r1_tarski(X19,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.15/0.39  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|v2_struct_0(X2)|~m2_orders_2(X1,X2,X3)|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_orders_1(X3,k1_orders_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.15/0.39  cnf(c_0_18, negated_conjecture, (m1_orders_1(esk2_0,k1_orders_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_20, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_21, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_22, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  fof(c_0_24, plain, ![X28, X29, X30, X31]:((~m1_orders_2(X30,X28,X31)|~m1_orders_2(X31,X28,X30)|X30=X31|~m2_orders_2(X31,X28,X29)|~m2_orders_2(X30,X28,X29)|~m1_orders_1(X29,k1_orders_1(u1_struct_0(X28)))|(v2_struct_0(X28)|~v3_orders_2(X28)|~v4_orders_2(X28)|~v5_orders_2(X28)|~l1_orders_2(X28)))&(m1_orders_2(X31,X28,X30)|m1_orders_2(X30,X28,X31)|X30=X31|~m2_orders_2(X31,X28,X29)|~m2_orders_2(X30,X28,X29)|~m1_orders_1(X29,k1_orders_1(u1_struct_0(X28)))|(v2_struct_0(X28)|~v3_orders_2(X28)|~v4_orders_2(X28)|~v5_orders_2(X28)|~l1_orders_2(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_orders_2])])])])])).
% 0.15/0.39  fof(c_0_25, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.15/0.39  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_27, negated_conjecture, (r2_xboole_0(esk3_0,esk4_0)|m1_orders_2(esk3_0,esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.15/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))|~m2_orders_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.39  cnf(c_0_30, plain, (m1_orders_2(X1,X2,X3)|m1_orders_2(X3,X2,X1)|X3=X1|v2_struct_0(X2)|~m2_orders_2(X1,X2,X4)|~m2_orders_2(X3,X2,X4)|~m1_orders_1(X4,k1_orders_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.15/0.39  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.15/0.39  cnf(c_0_32, negated_conjecture, (m1_orders_2(esk3_0,esk1_0,esk4_0)|r1_tarski(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.15/0.39  cnf(c_0_33, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_34, negated_conjecture, (r1_tarski(X1,X2)|~m1_orders_2(X1,esk1_0,X2)|~m2_orders_2(X2,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.39  cnf(c_0_35, negated_conjecture, (X1=X2|m1_orders_2(X1,esk1_0,X2)|m1_orders_2(X2,esk1_0,X1)|~m2_orders_2(X2,esk1_0,esk2_0)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.39  cnf(c_0_36, negated_conjecture, (m2_orders_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_37, negated_conjecture, (esk4_0=esk3_0|m1_orders_2(esk3_0,esk1_0,esk4_0)|~r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.15/0.39  cnf(c_0_38, negated_conjecture, (m2_orders_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  fof(c_0_39, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|~v1_xboole_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.15/0.39  fof(c_0_40, plain, ![X9, X10]:(~r2_hidden(X9,X10)|m1_subset_1(k1_tarski(X9),k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.15/0.39  fof(c_0_41, plain, ![X25, X26, X27]:(v2_struct_0(X25)|~v3_orders_2(X25)|~v4_orders_2(X25)|~v5_orders_2(X25)|~l1_orders_2(X25)|(~m1_orders_1(X26,k1_orders_1(u1_struct_0(X25)))|(~m2_orders_2(X27,X25,X26)|r2_hidden(k1_funct_1(X26,u1_struct_0(X25)),X27)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_orders_2])])])])).
% 0.15/0.39  fof(c_0_42, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(X21=k1_xboole_0|~m1_orders_2(X21,X20,X22)|~m1_orders_2(X22,X20,X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t69_orders_2])])])])).
% 0.15/0.39  cnf(c_0_43, negated_conjecture, (X1=X2|r2_xboole_0(X1,X2)|~m1_orders_2(X1,esk1_0,X2)|~m2_orders_2(X2,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.15/0.39  cnf(c_0_44, negated_conjecture, (X1=esk4_0|m1_orders_2(esk4_0,esk1_0,X1)|m1_orders_2(X1,esk1_0,esk4_0)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.15/0.39  cnf(c_0_45, negated_conjecture, (esk4_0=esk3_0|m1_orders_2(esk3_0,esk1_0,esk4_0)|~m1_orders_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_38])])).
% 0.15/0.39  cnf(c_0_46, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.15/0.39  cnf(c_0_47, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.15/0.39  cnf(c_0_48, plain, (v2_struct_0(X1)|r2_hidden(k1_funct_1(X2,u1_struct_0(X1)),X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))|~m2_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.15/0.39  fof(c_0_49, plain, ![X23, X24]:(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|(~m1_orders_1(X24,k1_orders_1(u1_struct_0(X23)))|m2_orders_2(k1_tarski(k1_funct_1(X24,u1_struct_0(X23))),X23,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_orders_2])])])])).
% 0.15/0.39  cnf(c_0_50, plain, (v2_struct_0(X1)|X2=k1_xboole_0|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X2,X1,X3)|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.15/0.39  cnf(c_0_51, negated_conjecture, (X1=esk4_0|r2_xboole_0(X1,esk4_0)|~m1_orders_2(X1,esk1_0,esk4_0)), inference(spm,[status(thm)],[c_0_43, c_0_36])).
% 0.15/0.39  cnf(c_0_52, negated_conjecture, (esk4_0=esk3_0|m1_orders_2(esk3_0,esk1_0,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_45])).
% 0.15/0.39  cnf(c_0_53, plain, (~r2_hidden(X1,k1_tarski(X2))|~r2_hidden(X2,X3)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.15/0.39  cnf(c_0_54, negated_conjecture, (r2_hidden(k1_funct_1(esk2_0,u1_struct_0(esk1_0)),X1)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.39  cnf(c_0_55, plain, (v2_struct_0(X1)|m2_orders_2(k1_tarski(k1_funct_1(X2,u1_struct_0(X1))),X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.15/0.39  cnf(c_0_56, negated_conjecture, (X1=k1_xboole_0|~m1_orders_2(X2,esk1_0,X1)|~m1_orders_2(X1,esk1_0,X2)|~m2_orders_2(X2,esk1_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_29]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.39  cnf(c_0_57, negated_conjecture, (~r2_xboole_0(esk3_0,esk4_0)|~m1_orders_2(esk3_0,esk1_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.15/0.39  cnf(c_0_58, negated_conjecture, (esk4_0=esk3_0|r2_xboole_0(esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.15/0.39  cnf(c_0_59, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.15/0.39  cnf(c_0_60, negated_conjecture, (~m2_orders_2(k1_tarski(X1),esk1_0,esk2_0)|~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.15/0.39  cnf(c_0_61, negated_conjecture, (m2_orders_2(k1_tarski(k1_funct_1(esk2_0,u1_struct_0(esk1_0))),esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.15/0.39  cnf(c_0_62, negated_conjecture, (X1=k1_xboole_0|~m1_orders_2(X2,esk1_0,X1)|~m1_orders_2(X1,esk1_0,X2)|~m2_orders_2(X2,esk1_0,esk2_0)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_56, c_0_29])).
% 0.15/0.39  cnf(c_0_63, negated_conjecture, (esk4_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_52])).
% 0.15/0.39  cnf(c_0_64, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_59])).
% 0.15/0.39  cnf(c_0_65, negated_conjecture, (~r2_hidden(k1_funct_1(esk2_0,u1_struct_0(esk1_0)),X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.15/0.39  cnf(c_0_66, negated_conjecture, (X1=k1_xboole_0|~m1_orders_2(esk3_0,esk1_0,X1)|~m1_orders_2(X1,esk1_0,esk3_0)|~m2_orders_2(X1,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_62, c_0_38])).
% 0.15/0.39  cnf(c_0_67, negated_conjecture, (m1_orders_2(esk3_0,esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_63]), c_0_63]), c_0_64])).
% 0.15/0.39  cnf(c_0_68, negated_conjecture, (~m2_orders_2(X1,esk1_0,esk2_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_65, c_0_54])).
% 0.15/0.39  cnf(c_0_69, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.15/0.39  cnf(c_0_70, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_67]), c_0_38])])).
% 0.15/0.39  cnf(c_0_71, negated_conjecture, (~m2_orders_2(k1_xboole_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.15/0.39  cnf(c_0_72, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_70]), c_0_71]), ['proof']).
% 0.15/0.39  # SZS output end CNFRefutation
% 0.15/0.39  # Proof object total steps             : 73
% 0.15/0.39  # Proof object clause steps            : 49
% 0.15/0.39  # Proof object formula steps           : 24
% 0.15/0.39  # Proof object conjectures             : 37
% 0.15/0.39  # Proof object clause conjectures      : 34
% 0.15/0.39  # Proof object formula conjectures     : 3
% 0.15/0.39  # Proof object initial clauses used    : 23
% 0.15/0.39  # Proof object initial formulas used   : 12
% 0.15/0.39  # Proof object generating inferences   : 23
% 0.15/0.39  # Proof object simplifying inferences  : 49
% 0.15/0.39  # Training examples: 0 positive, 0 negative
% 0.15/0.39  # Parsed axioms                        : 12
% 0.15/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.15/0.39  # Initial clauses                      : 27
% 0.15/0.39  # Removed in clause preprocessing      : 0
% 0.15/0.39  # Initial clauses in saturation        : 27
% 0.15/0.39  # Processed clauses                    : 97
% 0.15/0.39  # ...of these trivial                  : 0
% 0.15/0.39  # ...subsumed                          : 7
% 0.15/0.39  # ...remaining for further processing  : 90
% 0.15/0.39  # Other redundant clauses eliminated   : 3
% 0.15/0.39  # Clauses deleted for lack of memory   : 0
% 0.15/0.39  # Backward-subsumed                    : 2
% 0.15/0.39  # Backward-rewritten                   : 17
% 0.15/0.39  # Generated clauses                    : 51
% 0.15/0.39  # ...of the previous two non-trivial   : 60
% 0.15/0.39  # Contextual simplify-reflections      : 2
% 0.15/0.39  # Paramodulations                      : 48
% 0.15/0.39  # Factorizations                       : 0
% 0.15/0.39  # Equation resolutions                 : 3
% 0.15/0.39  # Propositional unsat checks           : 0
% 0.15/0.39  #    Propositional check models        : 0
% 0.15/0.39  #    Propositional check unsatisfiable : 0
% 0.15/0.39  #    Propositional clauses             : 0
% 0.15/0.39  #    Propositional clauses after purity: 0
% 0.15/0.39  #    Propositional unsat core size     : 0
% 0.15/0.39  #    Propositional preprocessing time  : 0.000
% 0.15/0.39  #    Propositional encoding time       : 0.000
% 0.15/0.39  #    Propositional solver time         : 0.000
% 0.15/0.39  #    Success case prop preproc time    : 0.000
% 0.15/0.39  #    Success case prop encoding time   : 0.000
% 0.15/0.39  #    Success case prop solver time     : 0.000
% 0.15/0.39  # Current number of processed clauses  : 42
% 0.15/0.39  #    Positive orientable unit clauses  : 9
% 0.15/0.39  #    Positive unorientable unit clauses: 0
% 0.15/0.39  #    Negative unit clauses             : 3
% 0.15/0.39  #    Non-unit-clauses                  : 30
% 0.15/0.39  # Current number of unprocessed clauses: 9
% 0.15/0.39  # ...number of literals in the above   : 41
% 0.15/0.39  # Current number of archived formulas  : 0
% 0.15/0.39  # Current number of archived clauses   : 45
% 0.15/0.39  # Clause-clause subsumption calls (NU) : 1075
% 0.15/0.39  # Rec. Clause-clause subsumption calls : 196
% 0.15/0.39  # Non-unit clause-clause subsumptions  : 10
% 0.15/0.39  # Unit Clause-clause subsumption calls : 19
% 0.15/0.39  # Rewrite failures with RHS unbound    : 0
% 0.15/0.39  # BW rewrite match attempts            : 4
% 0.15/0.39  # BW rewrite match successes           : 2
% 0.15/0.39  # Condensation attempts                : 0
% 0.15/0.39  # Condensation successes               : 0
% 0.15/0.39  # Termbank termtop insertions          : 4340
% 0.15/0.39  
% 0.15/0.39  # -------------------------------------------------
% 0.15/0.39  # User time                : 0.027 s
% 0.15/0.39  # System time              : 0.003 s
% 0.15/0.39  # Total time               : 0.030 s
% 0.15/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
