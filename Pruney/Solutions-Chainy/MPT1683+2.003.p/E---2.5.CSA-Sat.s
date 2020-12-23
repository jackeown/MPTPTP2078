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
% DateTime   : Thu Dec  3 11:16:29 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 113 expanded)
%              Number of clauses        :   32 (  38 expanded)
%              Number of leaves         :    7 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :  279 (1260 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_waybel_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> v5_yellow_0(k5_yellow_0(X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_waybel_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(d16_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v5_yellow_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,u1_struct_0(X2))
                        & r2_hidden(X4,u1_struct_0(X2))
                        & r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)) )
                     => r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_yellow_0)).

fof(t40_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t21_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v2_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r2_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_yellow_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( ( ~ v1_xboole_0(X2)
                & v2_waybel_0(X2,X1)
                & v13_waybel_0(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            <=> v5_yellow_0(k5_yellow_0(X1,X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_waybel_0])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] :
      ( v1_xboole_0(X8)
      | ~ m1_subset_1(X9,X8)
      | ~ m1_subset_1(X10,X8)
      | k7_domain_1(X8,X9,X10) = k2_tarski(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

fof(c_0_9,negated_conjecture,
    ( v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & v2_lattice3(esk5_0)
    & l1_orders_2(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v13_waybel_0(esk6_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ( v1_xboole_0(esk6_0)
      | ~ v2_waybel_0(esk6_0,esk5_0)
      | ~ v13_waybel_0(esk6_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      | ~ v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) )
    & ( ~ v1_xboole_0(esk6_0)
      | v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) )
    & ( v2_waybel_0(esk6_0,esk5_0)
      | v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) )
    & ( v13_waybel_0(esk6_0,esk5_0)
      | v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) )
    & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
      | v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v5_yellow_0(X13,X12)
        | ~ m1_subset_1(X14,u1_struct_0(X12))
        | ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X14,u1_struct_0(X13))
        | ~ r2_hidden(X15,u1_struct_0(X13))
        | ~ r2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),X14,X15))
        | r2_hidden(k2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),X14,X15)),u1_struct_0(X13))
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))
        | v5_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),u1_struct_0(X12))
        | v5_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk1_2(X12,X13),u1_struct_0(X13))
        | v5_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_hidden(esk2_2(X12,X13),u1_struct_0(X13))
        | v5_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( r2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),esk1_2(X12,X13),esk2_2(X12,X13)))
        | v5_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) )
      & ( ~ r2_hidden(k2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),esk1_2(X12,X13),esk2_2(X12,X13))),u1_struct_0(X13))
        | v5_yellow_0(X13,X12)
        | ~ m1_yellow_0(X13,X12)
        | v2_struct_0(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_yellow_0])])])])])])).

fof(c_0_11,plain,(
    ! [X23,X24,X25] :
      ( ~ v3_orders_2(X23)
      | ~ v4_orders_2(X23)
      | ~ v5_orders_2(X23)
      | ~ v2_lattice3(X23)
      | ~ l1_orders_2(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_subset_1(X25,u1_struct_0(X23))
      | k2_yellow_0(X23,k7_domain_1(u1_struct_0(X23),X24,X25)) = k12_lattice3(X23,X24,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).

fof(c_0_12,plain,(
    ! [X11] :
      ( ~ l1_orders_2(X11)
      | ~ v2_lattice3(X11)
      | ~ v2_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_16,plain,
    ( v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2))),u1_struct_0(X2))
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_17,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_20,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_21,plain,
    ( r2_hidden(k2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ v5_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),X1,esk6_0) = k2_tarski(X1,esk6_0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

fof(c_0_24,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_lattice3(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X18))
        | r2_yellow_0(X18,k2_tarski(X19,X20))
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk3_1(X18),u1_struct_0(X18))
        | v2_lattice3(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk4_1(X18),u1_struct_0(X18))
        | v2_lattice3(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) )
      & ( ~ r2_yellow_0(X18,k2_tarski(esk3_1(X18),esk4_1(X18)))
        | v2_lattice3(X18)
        | ~ v5_orders_2(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).

cnf(c_0_25,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v2_waybel_0(esk6_0,esk5_0)
    | ~ v13_waybel_0(esk6_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_30,plain,
    ( v5_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(k12_lattice3(X2,esk1_2(X2,X1),esk2_2(X2,X1)),u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),
    [final]).

cnf(c_0_31,plain,
    ( r2_hidden(k12_lattice3(X1,X2,X3),u1_struct_0(X4))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
    | ~ v5_yellow_0(X4,X1)
    | ~ m1_yellow_0(X4,X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X4))
    | ~ r2_hidden(X2,u1_struct_0(X4)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_17]),c_0_20]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),esk6_0,esk6_0) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14]),
    [final]).

cnf(c_0_34,plain,
    ( r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2)))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_struct_0(X2))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_2(X1,X2),u1_struct_0(X2))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_37,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_38,plain,
    ( v2_lattice3(X1)
    | ~ r2_yellow_0(X1,k2_tarski(esk3_1(X1),esk4_1(X1)))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_39,plain,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(X1))
    | v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_40,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_waybel_0(esk6_0,esk5_0)
    | ~ v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_14])]),c_0_27]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( v2_waybel_0(esk6_0,esk5_0)
    | v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_28]),c_0_29])]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:41:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.14/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(t63_waybel_0, conjecture, ![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(((~(v1_xboole_0(X2))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>v5_yellow_0(k5_yellow_0(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_waybel_0)).
% 0.14/0.38  fof(redefinition_k7_domain_1, axiom, ![X1, X2, X3]:(((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))&m1_subset_1(X3,X1))=>k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 0.14/0.38  fof(d16_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_yellow_0(X2,X1)=>(v5_yellow_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_hidden(X3,u1_struct_0(X2))&r2_hidden(X4,u1_struct_0(X2)))&r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)))=>r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)),u1_struct_0(X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_yellow_0)).
% 0.14/0.38  fof(t40_yellow_0, axiom, ![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))=k12_lattice3(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_yellow_0)).
% 0.14/0.38  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.14/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.38  fof(t21_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>(v2_lattice3(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r2_yellow_0(X1,k2_tarski(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_yellow_0)).
% 0.14/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(((~(v1_xboole_0(X2))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>v5_yellow_0(k5_yellow_0(X1,X2),X1))))), inference(assume_negation,[status(cth)],[t63_waybel_0])).
% 0.14/0.38  fof(c_0_8, plain, ![X8, X9, X10]:(v1_xboole_0(X8)|~m1_subset_1(X9,X8)|~m1_subset_1(X10,X8)|k7_domain_1(X8,X9,X10)=k2_tarski(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).
% 0.14/0.38  fof(c_0_9, negated_conjecture, (((((v3_orders_2(esk5_0)&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v2_lattice3(esk5_0))&l1_orders_2(esk5_0))&(((~v1_xboole_0(esk6_0)&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((v1_xboole_0(esk6_0)|~v2_waybel_0(esk6_0,esk5_0)|~v13_waybel_0(esk6_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0))&((((~v1_xboole_0(esk6_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0))&(v2_waybel_0(esk6_0,esk5_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)))&(v13_waybel_0(esk6_0,esk5_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])])).
% 0.14/0.38  fof(c_0_10, plain, ![X12, X13, X14, X15]:((~v5_yellow_0(X13,X12)|(~m1_subset_1(X14,u1_struct_0(X12))|(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X14,u1_struct_0(X13))|~r2_hidden(X15,u1_struct_0(X13))|~r2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),X14,X15))|r2_hidden(k2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),X14,X15)),u1_struct_0(X13)))))|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12)))&((m1_subset_1(esk1_2(X12,X13),u1_struct_0(X12))|v5_yellow_0(X13,X12)|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12)))&((m1_subset_1(esk2_2(X12,X13),u1_struct_0(X12))|v5_yellow_0(X13,X12)|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12)))&((((r2_hidden(esk1_2(X12,X13),u1_struct_0(X13))|v5_yellow_0(X13,X12)|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12)))&(r2_hidden(esk2_2(X12,X13),u1_struct_0(X13))|v5_yellow_0(X13,X12)|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12))))&(r2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),esk1_2(X12,X13),esk2_2(X12,X13)))|v5_yellow_0(X13,X12)|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12))))&(~r2_hidden(k2_yellow_0(X12,k7_domain_1(u1_struct_0(X12),esk1_2(X12,X13),esk2_2(X12,X13))),u1_struct_0(X13))|v5_yellow_0(X13,X12)|~m1_yellow_0(X13,X12)|(v2_struct_0(X12)|~l1_orders_2(X12))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_yellow_0])])])])])])).
% 0.14/0.38  fof(c_0_11, plain, ![X23, X24, X25]:(~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~v2_lattice3(X23)|~l1_orders_2(X23)|(~m1_subset_1(X24,u1_struct_0(X23))|(~m1_subset_1(X25,u1_struct_0(X23))|k2_yellow_0(X23,k7_domain_1(u1_struct_0(X23),X24,X25))=k12_lattice3(X23,X24,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X11]:(~l1_orders_2(X11)|(~v2_lattice3(X11)|~v2_struct_0(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.14/0.38  cnf(c_0_13, plain, (v1_xboole_0(X1)|k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  fof(c_0_15, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.38  cnf(c_0_16, plain, (v5_yellow_0(X2,X1)|v2_struct_0(X1)|~r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2))),u1_struct_0(X2))|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_17, plain, (k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))=k12_lattice3(X1,X2,X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.14/0.38  cnf(c_0_18, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_19, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_20, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(k2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X1))|v2_struct_0(X2)|~v5_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,u1_struct_0(X1))|~r2_hidden(X4,u1_struct_0(X1))|~r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),X1,esk6_0)=k2_tarski(X1,esk6_0)|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_23, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.14/0.38  fof(c_0_24, plain, ![X18, X19, X20]:((~v2_lattice3(X18)|(~m1_subset_1(X19,u1_struct_0(X18))|(~m1_subset_1(X20,u1_struct_0(X18))|r2_yellow_0(X18,k2_tarski(X19,X20))))|(~v5_orders_2(X18)|~l1_orders_2(X18)))&((m1_subset_1(esk3_1(X18),u1_struct_0(X18))|v2_lattice3(X18)|(~v5_orders_2(X18)|~l1_orders_2(X18)))&((m1_subset_1(esk4_1(X18),u1_struct_0(X18))|v2_lattice3(X18)|(~v5_orders_2(X18)|~l1_orders_2(X18)))&(~r2_yellow_0(X18,k2_tarski(esk3_1(X18),esk4_1(X18)))|v2_lattice3(X18)|(~v5_orders_2(X18)|~l1_orders_2(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (v1_xboole_0(esk6_0)|~v2_waybel_0(esk6_0,esk5_0)|~v13_waybel_0(esk6_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v2_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_30, plain, (v5_yellow_0(X1,X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~v5_orders_2(X2)|~m1_yellow_0(X1,X2)|~v2_lattice3(X2)|~l1_orders_2(X2)|~r2_hidden(k12_lattice3(X2,esk1_2(X2,X1),esk2_2(X2,X1)),u1_struct_0(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_31, plain, (r2_hidden(k12_lattice3(X1,X2,X3),u1_struct_0(X4))|~v4_orders_2(X1)|~v3_orders_2(X1)|~v5_orders_2(X1)|~r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))|~v5_yellow_0(X4,X1)|~m1_yellow_0(X4,X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X4))|~r2_hidden(X2,u1_struct_0(X4))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_17]), c_0_20]), ['final']).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),esk6_0,esk6_0)=k2_tarski(esk6_0,esk6_0)|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_22, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_23, c_0_14]), ['final']).
% 0.14/0.38  cnf(c_0_34, plain, (r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2)))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_35, plain, (r2_hidden(esk2_2(X1,X2),u1_struct_0(X2))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_36, plain, (r2_hidden(esk1_2(X1,X2),u1_struct_0(X2))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_37, plain, (r2_yellow_0(X1,k2_tarski(X2,X3))|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_38, plain, (v2_lattice3(X1)|~r2_yellow_0(X1,k2_tarski(esk3_1(X1),esk4_1(X1)))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_39, plain, (m1_subset_1(esk4_1(X1),u1_struct_0(X1))|v2_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_40, plain, (m1_subset_1(esk3_1(X1),u1_struct_0(X1))|v2_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (~v2_waybel_0(esk6_0,esk5_0)|~v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_14])]), c_0_27]), ['final']).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (v2_waybel_0(esk6_0,esk5_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_28]), c_0_29])]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 47
% 0.14/0.38  # Proof object clause steps            : 32
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 18
% 0.14/0.38  # Proof object clause conjectures      : 15
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 25
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 10
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 28
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 28
% 0.14/0.38  # Processed clauses                    : 34
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 1
% 0.14/0.38  # ...remaining for further processing  : 31
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 10
% 0.14/0.38  # ...of the previous two non-trivial   : 6
% 0.14/0.38  # Contextual simplify-reflections      : 4
% 0.14/0.38  # Paramodulations                      : 10
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 31
% 0.14/0.38  #    Positive orientable unit clauses  : 7
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 22
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 0
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 116
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 5
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.14/0.38  # Unit Clause-clause subsumption calls : 1
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2913
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.033 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
