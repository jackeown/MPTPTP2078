%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:51 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 782 expanded)
%              Number of clauses        :   46 ( 275 expanded)
%              Number of leaves         :    9 ( 187 expanded)
%              Depth                    :   16
%              Number of atoms          :  318 (5457 expanded)
%              Number of equality atoms :   46 ( 248 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(t35_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
            & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_orders_2(X1,X2,X3)
                <=> r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_orders_2])).

fof(c_0_10,plain,(
    ! [X27,X28] :
      ( v1_xboole_0(X27)
      | ~ m1_subset_1(X28,X27)
      | k6_domain_1(X27,X28) = k1_tarski(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_11,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X20,X21,X22,X24,X25] :
      ( ( m1_subset_1(esk2_3(X20,X21,X22),u1_struct_0(X21))
        | ~ r2_hidden(X20,a_2_0_orders_2(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))) )
      & ( X20 = esk2_3(X20,X21,X22)
        | ~ r2_hidden(X20,a_2_0_orders_2(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ r2_hidden(X24,X22)
        | r2_orders_2(X21,X24,esk2_3(X20,X21,X22))
        | ~ r2_hidden(X20,a_2_0_orders_2(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))) )
      & ( m1_subset_1(esk3_4(X20,X21,X22,X25),u1_struct_0(X21))
        | ~ m1_subset_1(X25,u1_struct_0(X21))
        | X20 != X25
        | r2_hidden(X20,a_2_0_orders_2(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))) )
      & ( r2_hidden(esk3_4(X20,X21,X22,X25),X22)
        | ~ m1_subset_1(X25,u1_struct_0(X21))
        | X20 != X25
        | r2_hidden(X20,a_2_0_orders_2(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))) )
      & ( ~ r2_orders_2(X21,esk3_4(X20,X21,X22,X25),X25)
        | ~ m1_subset_1(X25,u1_struct_0(X21))
        | X20 != X25
        | r2_hidden(X20,a_2_0_orders_2(X21,X22))
        | v2_struct_0(X21)
        | ~ v3_orders_2(X21)
        | ~ v4_orders_2(X21)
        | ~ v5_orders_2(X21)
        | ~ l1_orders_2(X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_13,plain,(
    ! [X29,X30] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X29),X30),X29)
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ l1_orders_2(X29) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X29),X30),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X30,u1_struct_0(X29))
        | v2_struct_0(X29)
        | ~ v3_orders_2(X29)
        | ~ l1_orders_2(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) )
    & ( r2_orders_2(esk4_0,esk5_0,esk6_0)
      | r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_24,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])]),c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_31,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk4_0,X1,esk6_0),X1)
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k1_orders_2(X17,X18) = a_2_0_orders_2(X17,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

cnf(c_0_35,plain,
    ( r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,esk3_4(X2,X1,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X2 != X4
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0),k2_tarski(esk5_0,esk5_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ r2_orders_2(X1,esk3_4(X2,X1,X3,X2),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))
    | ~ r2_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_26]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22]),c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,plain,
    ( r2_orders_2(X2,X1,esk2_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,k2_tarski(X2,X4)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tarski(X2,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,k2_tarski(X2,X4))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_30])).

cnf(c_0_51,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_53,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_19]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22]),c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_50]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22]),c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_57,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ l1_struct_0(X16)
      | ~ v1_xboole_0(u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_30]),c_0_50])).

fof(c_0_61,plain,(
    ! [X19] :
      ( ~ l1_orders_2(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_62,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_22])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.14/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t51_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_orders_2)).
% 0.14/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.39  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.14/0.39  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 0.14/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.14/0.39  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 0.14/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.39  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))))), inference(assume_negation,[status(cth)],[t51_orders_2])).
% 0.14/0.39  fof(c_0_10, plain, ![X27, X28]:(v1_xboole_0(X27)|~m1_subset_1(X28,X27)|k6_domain_1(X27,X28)=k1_tarski(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.39  fof(c_0_11, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.39  fof(c_0_12, plain, ![X20, X21, X22, X24, X25]:((((m1_subset_1(esk2_3(X20,X21,X22),u1_struct_0(X21))|~r2_hidden(X20,a_2_0_orders_2(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))))&(X20=esk2_3(X20,X21,X22)|~r2_hidden(X20,a_2_0_orders_2(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))))))&(~m1_subset_1(X24,u1_struct_0(X21))|(~r2_hidden(X24,X22)|r2_orders_2(X21,X24,esk2_3(X20,X21,X22)))|~r2_hidden(X20,a_2_0_orders_2(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))))))&((m1_subset_1(esk3_4(X20,X21,X22,X25),u1_struct_0(X21))|(~m1_subset_1(X25,u1_struct_0(X21))|X20!=X25)|r2_hidden(X20,a_2_0_orders_2(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))))&((r2_hidden(esk3_4(X20,X21,X22,X25),X22)|(~m1_subset_1(X25,u1_struct_0(X21))|X20!=X25)|r2_hidden(X20,a_2_0_orders_2(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))))&(~r2_orders_2(X21,esk3_4(X20,X21,X22,X25),X25)|(~m1_subset_1(X25,u1_struct_0(X21))|X20!=X25)|r2_hidden(X20,a_2_0_orders_2(X21,X22))|(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.14/0.39  fof(c_0_13, plain, ![X29, X30]:((v6_orders_2(k6_domain_1(u1_struct_0(X29),X30),X29)|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v3_orders_2(X29)|~l1_orders_2(X29)))&(m1_subset_1(k6_domain_1(u1_struct_0(X29),X30),k1_zfmisc_1(u1_struct_0(X29)))|~m1_subset_1(X30,u1_struct_0(X29))|(v2_struct_0(X29)|~v3_orders_2(X29)|~l1_orders_2(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.14/0.39  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))))&(r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.14/0.39  cnf(c_0_15, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_17, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_0_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_18, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_23, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.39  fof(c_0_24, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.14/0.39  cnf(c_0_25, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.14/0.39  cnf(c_0_31, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk4_0,X1,esk6_0),X1)|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  fof(c_0_34, plain, ![X17, X18]:(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k1_orders_2(X17,X18)=a_2_0_orders_2(X17,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.14/0.39  cnf(c_0_35, plain, (r2_hidden(X2,a_2_0_orders_2(X1,X3))|v2_struct_0(X1)|~r2_orders_2(X1,esk3_4(X2,X1,X3,X4),X4)|~m1_subset_1(X4,u1_struct_0(X1))|X2!=X4|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_36, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0),k2_tarski(esk5_0,esk5_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.39  cnf(c_0_38, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.39  cnf(c_0_39, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~r2_orders_2(X1,esk3_4(X2,X1,X3,X2),X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0)=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_29]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.14/0.39  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))|~r2_orders_2(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_26]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22]), c_0_33])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.39  cnf(c_0_46, plain, (r2_orders_2(X2,X1,esk2_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_47, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.14/0.39  cnf(c_0_49, plain, (r2_orders_2(X1,X2,esk2_3(X3,X1,k2_tarski(X2,X4)))|v2_struct_0(X1)|~m1_subset_1(k2_tarski(X2,X4),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X3,a_2_0_orders_2(X1,k2_tarski(X2,X4)))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_48, c_0_30])).
% 0.14/0.39  cnf(c_0_51, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_19]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22]), c_0_33])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0))=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_50]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22]), c_0_33])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(rw,[status(thm)],[c_0_52, c_0_42])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.14/0.39  fof(c_0_57, plain, ![X16]:(v2_struct_0(X16)|~l1_struct_0(X16)|~v1_xboole_0(u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.14/0.39  cnf(c_0_59, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_30]), c_0_50])).
% 0.14/0.39  fof(c_0_61, plain, ![X19]:(~l1_orders_2(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_22])).
% 0.14/0.39  cnf(c_0_63, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.14/0.39  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_20])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 65
% 0.14/0.39  # Proof object clause steps            : 46
% 0.14/0.39  # Proof object formula steps           : 19
% 0.14/0.39  # Proof object conjectures             : 31
% 0.14/0.39  # Proof object clause conjectures      : 28
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 21
% 0.14/0.39  # Proof object initial formulas used   : 9
% 0.14/0.39  # Proof object generating inferences   : 18
% 0.14/0.39  # Proof object simplifying inferences  : 51
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 9
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 28
% 0.14/0.39  # Removed in clause preprocessing      : 1
% 0.14/0.39  # Initial clauses in saturation        : 27
% 0.14/0.39  # Processed clauses                    : 143
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 12
% 0.14/0.39  # ...remaining for further processing  : 131
% 0.14/0.39  # Other redundant clauses eliminated   : 26
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 5
% 0.14/0.39  # Backward-rewritten                   : 27
% 0.14/0.39  # Generated clauses                    : 248
% 0.14/0.39  # ...of the previous two non-trivial   : 219
% 0.14/0.39  # Contextual simplify-reflections      : 6
% 0.14/0.39  # Paramodulations                      : 212
% 0.14/0.39  # Factorizations                       : 12
% 0.14/0.39  # Equation resolutions                 : 26
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 66
% 0.14/0.39  #    Positive orientable unit clauses  : 15
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 2
% 0.14/0.39  #    Non-unit-clauses                  : 49
% 0.14/0.39  # Current number of unprocessed clauses: 128
% 0.14/0.39  # ...number of literals in the above   : 553
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 60
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1463
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 389
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 23
% 0.14/0.39  # Unit Clause-clause subsumption calls : 25
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 4
% 0.14/0.39  # BW rewrite match successes           : 2
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 10751
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.041 s
% 0.14/0.39  # System time              : 0.003 s
% 0.14/0.39  # Total time               : 0.045 s
% 0.14/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
