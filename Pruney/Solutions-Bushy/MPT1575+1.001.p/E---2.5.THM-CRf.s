%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1575+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:25 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 193 expanded)
%              Number of clauses        :   27 (  76 expanded)
%              Number of leaves         :    8 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 ( 866 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t53_yellow_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ( ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
       => v3_lattice3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_yellow_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(d9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_yellow_0(X1,X2)
           => ( X3 = k1_yellow_0(X1,X2)
            <=> ( r2_lattice3(X1,X2,X3)
                & ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_lattice3(X1,X2,X4)
                     => r1_orders_2(X1,X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(d12_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r2_lattice3(X1,X2,X3)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_lattice3)).

fof(t50_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( r1_yellow_0(X1,X2)
           => r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r1_yellow_0(X1,X2) )
          & ( r2_yellow_0(X1,X2)
           => r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1))) )
          & ( r2_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_yellow_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => r1_yellow_0(X1,X2) )
         => v3_lattice3(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t53_yellow_0])).

fof(c_0_9,negated_conjecture,(
    ! [X28] :
      ( ~ v2_struct_0(esk5_0)
      & l1_orders_2(esk5_0)
      & ( ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(esk5_0)))
        | r1_yellow_0(esk5_0,X28) )
      & ~ v3_lattice3(esk5_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_10,plain,(
    ! [X23,X24] :
      ( ( ~ m1_subset_1(X23,k1_zfmisc_1(X24))
        | r1_tarski(X23,X24) )
      & ( ~ r1_tarski(X23,X24)
        | m1_subset_1(X23,k1_zfmisc_1(X24)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_11,negated_conjecture,
    ( r1_yellow_0(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X21,X22] : r1_tarski(k3_xboole_0(X21,X22),X21) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16,X17] :
      ( ( r2_lattice3(X14,X15,X16)
        | X16 != k1_yellow_0(X14,X15)
        | ~ r1_yellow_0(X14,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_lattice3(X14,X15,X17)
        | r1_orders_2(X14,X16,X17)
        | X16 != k1_yellow_0(X14,X15)
        | ~ r1_yellow_0(X14,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk4_3(X14,X15,X16),u1_struct_0(X14))
        | ~ r2_lattice3(X14,X15,X16)
        | X16 = k1_yellow_0(X14,X15)
        | ~ r1_yellow_0(X14,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( r2_lattice3(X14,X15,esk4_3(X14,X15,X16))
        | ~ r2_lattice3(X14,X15,X16)
        | X16 = k1_yellow_0(X14,X15)
        | ~ r1_yellow_0(X14,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) )
      & ( ~ r1_orders_2(X14,X16,esk4_3(X14,X15,X16))
        | ~ r2_lattice3(X14,X15,X16)
        | X16 = k1_yellow_0(X14,X15)
        | ~ r1_yellow_0(X14,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_yellow_0])])])])])).

fof(c_0_15,plain,(
    ! [X19,X20] :
      ( ~ l1_orders_2(X19)
      | m1_subset_1(k1_yellow_0(X19,X20),u1_struct_0(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_16,negated_conjecture,
    ( r1_yellow_0(esk5_0,X1)
    | ~ r1_tarski(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_19,plain,(
    ! [X7,X8,X10,X12] :
      ( ( m1_subset_1(esk1_2(X7,X8),u1_struct_0(X7))
        | ~ v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,X8,esk1_2(X7,X8))
        | ~ v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_lattice3(X7,X8,X10)
        | r1_orders_2(X7,esk1_2(X7,X8),X10)
        | ~ v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk3_2(X7,X12),u1_struct_0(X7))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r2_lattice3(X7,esk2_1(X7),X12)
        | v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( r2_lattice3(X7,esk2_1(X7),esk3_2(X7,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r2_lattice3(X7,esk2_1(X7),X12)
        | v3_lattice3(X7)
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,X12,esk3_2(X7,X12))
        | ~ m1_subset_1(X12,u1_struct_0(X7))
        | ~ r2_lattice3(X7,esk2_1(X7),X12)
        | v3_lattice3(X7)
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_20,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X25,X26] :
      ( ( ~ r1_yellow_0(X25,X26)
        | r1_yellow_0(X25,k3_xboole_0(X26,u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r1_yellow_0(X25,k3_xboole_0(X26,u1_struct_0(X25)))
        | r1_yellow_0(X25,X26)
        | v2_struct_0(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r2_yellow_0(X25,X26)
        | r2_yellow_0(X25,k3_xboole_0(X26,u1_struct_0(X25)))
        | v2_struct_0(X25)
        | ~ l1_orders_2(X25) )
      & ( ~ r2_yellow_0(X25,k3_xboole_0(X26,u1_struct_0(X25)))
        | r2_yellow_0(X25,X26)
        | v2_struct_0(X25)
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_yellow_0])])])])])).

cnf(c_0_23,negated_conjecture,
    ( r1_yellow_0(esk5_0,k3_xboole_0(u1_struct_0(esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21])).

cnf(c_0_28,plain,
    ( r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,k3_xboole_0(X2,u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_yellow_0(esk5_0,k3_xboole_0(X1,u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_21])).

cnf(c_0_35,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,k1_yellow_0(X1,esk2_1(X1))))
    | v3_lattice3(X1)
    | ~ r1_yellow_0(X1,esk2_1(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( r1_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( ~ v3_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk3_2(X1,k1_yellow_0(X1,esk2_1(X1))),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ r1_yellow_0(X1,esk2_1(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_21])).

cnf(c_0_39,plain,
    ( v3_lattice3(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,esk3_2(X1,k1_yellow_0(X1,X2)))
    | ~ r2_lattice3(X1,esk2_1(X1),k1_yellow_0(X1,X2))
    | ~ m1_subset_1(esk3_2(X1,k1_yellow_0(X1,X2)),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( r2_lattice3(esk5_0,esk2_1(esk5_0),esk3_2(esk5_0,k1_yellow_0(esk5_0,esk2_1(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_30])]),c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk3_2(esk5_0,k1_yellow_0(esk5_0,esk2_1(esk5_0))),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_30])]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_lattice3(esk5_0,esk2_1(esk5_0),k1_yellow_0(esk5_0,esk2_1(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_36]),c_0_41]),c_0_30])]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_27]),c_0_36]),c_0_30])]),
    [proof]).

%------------------------------------------------------------------------------
