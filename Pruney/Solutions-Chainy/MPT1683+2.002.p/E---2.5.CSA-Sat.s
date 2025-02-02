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
% DateTime   : Thu Dec  3 11:16:29 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 112 expanded)
%              Number of clauses        :   33 (  38 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :  286 (1219 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_waybel_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_yellow_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_yellow_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_0)).

fof(c_0_8,negated_conjecture,(
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

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( v1_xboole_0(X7)
      | ~ m1_subset_1(X8,X7)
      | ~ m1_subset_1(X9,X7)
      | k7_domain_1(X7,X8,X9) = k2_tarski(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

fof(c_0_10,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v5_yellow_0(X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X13,u1_struct_0(X12))
        | ~ r2_hidden(X14,u1_struct_0(X12))
        | ~ r2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),X13,X14))
        | r2_hidden(k2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),X13,X14)),u1_struct_0(X12))
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))
        | v5_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk2_2(X11,X12),u1_struct_0(X11))
        | v5_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk1_2(X11,X12),u1_struct_0(X12))
        | v5_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk2_2(X11,X12),u1_struct_0(X12))
        | v5_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( r2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),esk1_2(X11,X12),esk2_2(X11,X12)))
        | v5_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) )
      & ( ~ r2_hidden(k2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),esk1_2(X11,X12),esk2_2(X11,X12))),u1_struct_0(X12))
        | v5_yellow_0(X12,X11)
        | ~ m1_yellow_0(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_yellow_0])])])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] :
      ( ~ v3_orders_2(X22)
      | ~ v4_orders_2(X22)
      | ~ v5_orders_2(X22)
      | ~ v2_lattice3(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | k2_yellow_0(X22,k7_domain_1(u1_struct_0(X22),X23,X24)) = k12_lattice3(X22,X23,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).

fof(c_0_13,plain,(
    ! [X10] :
      ( ~ l1_orders_2(X10)
      | ~ v2_lattice3(X10)
      | ~ v2_struct_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

fof(c_0_16,plain,(
    ! [X5] :
      ( v2_struct_0(X5)
      | ~ l1_struct_0(X5)
      | ~ v1_xboole_0(u1_struct_0(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_17,plain,(
    ! [X6] :
      ( ~ l1_orders_2(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_18,plain,
    ( v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2))),u1_struct_0(X2))
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_19,plain,
    ( k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k12_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_22,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),X1,esk6_0) = k2_tarski(X1,esk6_0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_26,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

fof(c_0_27,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_lattice3(X17)
        | ~ m1_subset_1(X18,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | r2_yellow_0(X17,k2_tarski(X18,X19))
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk3_1(X17),u1_struct_0(X17))
        | v2_lattice3(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk4_1(X17),u1_struct_0(X17))
        | v2_lattice3(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) )
      & ( ~ r2_yellow_0(X17,k2_tarski(esk3_1(X17),esk4_1(X17)))
        | v2_lattice3(X17)
        | ~ v5_orders_2(X17)
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v2_waybel_0(esk6_0,esk5_0)
    | ~ v13_waybel_0(esk6_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( v13_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( v2_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_33,plain,
    ( v5_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ r2_hidden(k12_lattice3(X2,esk1_2(X2,X1),esk2_2(X2,X1)),u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),
    [final]).

cnf(c_0_34,plain,
    ( r2_hidden(k12_lattice3(X1,X2,X3),u1_struct_0(X4))
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
    | ~ r2_hidden(X3,u1_struct_0(X4))
    | ~ r2_hidden(X2,u1_struct_0(X4))
    | ~ v5_yellow_0(X4,X1)
    | ~ m1_yellow_0(X4,X1)
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_22]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),esk6_0,esk6_0) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_15]),
    [final]).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_37,plain,
    ( r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2)))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_struct_0(X2))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),u1_struct_0(X2))
    | v5_yellow_0(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_yellow_0(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_40,plain,
    ( r2_yellow_0(X1,k2_tarski(X2,X3))
    | ~ v2_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_41,plain,
    ( m1_subset_1(esk4_1(X1),u1_struct_0(X1))
    | v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_42,plain,
    ( m1_subset_1(esk3_1(X1),u1_struct_0(X1))
    | v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_43,plain,
    ( v2_lattice3(X1)
    | ~ r2_yellow_0(X1,k2_tarski(esk3_1(X1),esk4_1(X1)))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v2_waybel_0(esk6_0,esk5_0)
    | v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_waybel_0(esk6_0,esk5_0)
    | ~ v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_15])]),c_0_30]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_31]),c_0_32])]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.37  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.029 s
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(t63_waybel_0, conjecture, ![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(((~(v1_xboole_0(X2))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>v5_yellow_0(k5_yellow_0(X1,X2),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_waybel_0)).
% 0.20/0.37  fof(redefinition_k7_domain_1, axiom, ![X1, X2, X3]:(((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))&m1_subset_1(X3,X1))=>k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 0.20/0.37  fof(d16_yellow_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_yellow_0(X2,X1)=>(v5_yellow_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(((r2_hidden(X3,u1_struct_0(X2))&r2_hidden(X4,u1_struct_0(X2)))&r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)))=>r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)),u1_struct_0(X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_yellow_0)).
% 0.20/0.37  fof(t40_yellow_0, axiom, ![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))=k12_lattice3(X1,X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_yellow_0)).
% 0.20/0.37  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.20/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.37  fof(t21_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>(v2_lattice3(X1)<=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>r2_yellow_0(X1,k2_tarski(X2,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_yellow_0)).
% 0.20/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(((~(v1_xboole_0(X2))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>v5_yellow_0(k5_yellow_0(X1,X2),X1))))), inference(assume_negation,[status(cth)],[t63_waybel_0])).
% 0.20/0.37  fof(c_0_9, plain, ![X7, X8, X9]:(v1_xboole_0(X7)|~m1_subset_1(X8,X7)|~m1_subset_1(X9,X7)|k7_domain_1(X7,X8,X9)=k2_tarski(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).
% 0.20/0.37  fof(c_0_10, negated_conjecture, (((((v3_orders_2(esk5_0)&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&v2_lattice3(esk5_0))&l1_orders_2(esk5_0))&(((~v1_xboole_0(esk6_0)&v13_waybel_0(esk6_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))))&((v1_xboole_0(esk6_0)|~v2_waybel_0(esk6_0,esk5_0)|~v13_waybel_0(esk6_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0))&((((~v1_xboole_0(esk6_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0))&(v2_waybel_0(esk6_0,esk5_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)))&(v13_waybel_0(esk6_0,esk5_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.20/0.37  fof(c_0_11, plain, ![X11, X12, X13, X14]:((~v5_yellow_0(X12,X11)|(~m1_subset_1(X13,u1_struct_0(X11))|(~m1_subset_1(X14,u1_struct_0(X11))|(~r2_hidden(X13,u1_struct_0(X12))|~r2_hidden(X14,u1_struct_0(X12))|~r2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),X13,X14))|r2_hidden(k2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),X13,X14)),u1_struct_0(X12)))))|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11)))&((m1_subset_1(esk1_2(X11,X12),u1_struct_0(X11))|v5_yellow_0(X12,X11)|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11)))&((m1_subset_1(esk2_2(X11,X12),u1_struct_0(X11))|v5_yellow_0(X12,X11)|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11)))&((((r2_hidden(esk1_2(X11,X12),u1_struct_0(X12))|v5_yellow_0(X12,X11)|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11)))&(r2_hidden(esk2_2(X11,X12),u1_struct_0(X12))|v5_yellow_0(X12,X11)|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11))))&(r2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),esk1_2(X11,X12),esk2_2(X11,X12)))|v5_yellow_0(X12,X11)|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11))))&(~r2_hidden(k2_yellow_0(X11,k7_domain_1(u1_struct_0(X11),esk1_2(X11,X12),esk2_2(X11,X12))),u1_struct_0(X12))|v5_yellow_0(X12,X11)|~m1_yellow_0(X12,X11)|(v2_struct_0(X11)|~l1_orders_2(X11))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d16_yellow_0])])])])])])).
% 0.20/0.37  fof(c_0_12, plain, ![X22, X23, X24]:(~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~v2_lattice3(X22)|~l1_orders_2(X22)|(~m1_subset_1(X23,u1_struct_0(X22))|(~m1_subset_1(X24,u1_struct_0(X22))|k2_yellow_0(X22,k7_domain_1(u1_struct_0(X22),X23,X24))=k12_lattice3(X22,X23,X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t40_yellow_0])])])).
% 0.20/0.37  fof(c_0_13, plain, ![X10]:(~l1_orders_2(X10)|(~v2_lattice3(X10)|~v2_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.20/0.37  cnf(c_0_14, plain, (v1_xboole_0(X1)|k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  fof(c_0_16, plain, ![X5]:(v2_struct_0(X5)|~l1_struct_0(X5)|~v1_xboole_0(u1_struct_0(X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.37  fof(c_0_17, plain, ![X6]:(~l1_orders_2(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.37  cnf(c_0_18, plain, (v5_yellow_0(X2,X1)|v2_struct_0(X1)|~r2_hidden(k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2))),u1_struct_0(X2))|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_19, plain, (k2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))=k12_lattice3(X1,X2,X3)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.20/0.37  cnf(c_0_20, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_21, plain, (m1_subset_1(esk2_2(X1,X2),u1_struct_0(X1))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_22, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.37  cnf(c_0_23, plain, (r2_hidden(k2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X1))|v2_struct_0(X2)|~v5_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,u1_struct_0(X1))|~r2_hidden(X4,u1_struct_0(X1))|~r2_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))|~m1_yellow_0(X1,X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),X1,esk6_0)=k2_tarski(X1,esk6_0)|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.20/0.37  cnf(c_0_25, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_26, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.37  fof(c_0_27, plain, ![X17, X18, X19]:((~v2_lattice3(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|(~m1_subset_1(X19,u1_struct_0(X17))|r2_yellow_0(X17,k2_tarski(X18,X19))))|(~v5_orders_2(X17)|~l1_orders_2(X17)))&((m1_subset_1(esk3_1(X17),u1_struct_0(X17))|v2_lattice3(X17)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&((m1_subset_1(esk4_1(X17),u1_struct_0(X17))|v2_lattice3(X17)|(~v5_orders_2(X17)|~l1_orders_2(X17)))&(~r2_yellow_0(X17,k2_tarski(esk3_1(X17),esk4_1(X17)))|v2_lattice3(X17)|(~v5_orders_2(X17)|~l1_orders_2(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_yellow_0])])])])])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (v1_xboole_0(esk6_0)|~v2_waybel_0(esk6_0,esk5_0)|~v13_waybel_0(esk6_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (v13_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (v2_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_33, plain, (v5_yellow_0(X1,X2)|~v4_orders_2(X2)|~v3_orders_2(X2)|~v5_orders_2(X2)|~r2_hidden(k12_lattice3(X2,esk1_2(X2,X1),esk2_2(X2,X1)),u1_struct_0(X1))|~m1_yellow_0(X1,X2)|~v2_lattice3(X2)|~l1_orders_2(X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_34, plain, (r2_hidden(k12_lattice3(X1,X2,X3),u1_struct_0(X4))|~v4_orders_2(X1)|~v3_orders_2(X1)|~v5_orders_2(X1)|~r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))|~r2_hidden(X3,u1_struct_0(X4))|~r2_hidden(X2,u1_struct_0(X4))|~v5_yellow_0(X4,X1)|~m1_yellow_0(X4,X1)|~v2_lattice3(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (k7_domain_1(k1_zfmisc_1(u1_struct_0(esk5_0)),esk6_0,esk6_0)=k2_tarski(esk6_0,esk6_0)|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_24, c_0_15]), ['final']).
% 0.20/0.37  cnf(c_0_36, plain, (v2_struct_0(X1)|~l1_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.20/0.37  cnf(c_0_37, plain, (r2_yellow_0(X1,k7_domain_1(u1_struct_0(X1),esk1_2(X1,X2),esk2_2(X1,X2)))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_38, plain, (r2_hidden(esk2_2(X1,X2),u1_struct_0(X2))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),u1_struct_0(X2))|v5_yellow_0(X2,X1)|v2_struct_0(X1)|~m1_yellow_0(X2,X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_40, plain, (r2_yellow_0(X1,k2_tarski(X2,X3))|~v2_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_41, plain, (m1_subset_1(esk4_1(X1),u1_struct_0(X1))|v2_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_42, plain, (m1_subset_1(esk3_1(X1),u1_struct_0(X1))|v2_lattice3(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_43, plain, (v2_lattice3(X1)|~r2_yellow_0(X1,k2_tarski(esk3_1(X1),esk4_1(X1)))|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_44, negated_conjecture, (v2_waybel_0(esk6_0,esk5_0)|v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (~v2_waybel_0(esk6_0,esk5_0)|~v5_yellow_0(k5_yellow_0(esk5_0,esk6_0),esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_15])]), c_0_30]), ['final']).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_31]), c_0_32])]), ['final']).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 50
% 0.20/0.37  # Proof object clause steps            : 33
% 0.20/0.37  # Proof object formula steps           : 17
% 0.20/0.37  # Proof object conjectures             : 17
% 0.20/0.37  # Proof object clause conjectures      : 14
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 26
% 0.20/0.37  # Proof object initial formulas used   : 8
% 0.20/0.37  # Proof object generating inferences   : 6
% 0.20/0.37  # Proof object simplifying inferences  : 10
% 0.20/0.37  # Parsed axioms                        : 8
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 29
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 29
% 0.20/0.37  # Processed clauses                    : 35
% 0.20/0.37  # ...of these trivial                  : 2
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 32
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 10
% 0.20/0.37  # ...of the previous two non-trivial   : 6
% 0.20/0.37  # Contextual simplify-reflections      : 4
% 0.20/0.37  # Paramodulations                      : 10
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 32
% 0.20/0.37  #    Positive orientable unit clauses  : 7
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 23
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 0
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 320
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 15
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.37  # Unit Clause-clause subsumption calls : 8
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 2958
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.031 s
% 0.20/0.37  # System time              : 0.004 s
% 0.20/0.37  # Total time               : 0.035 s
% 0.20/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
