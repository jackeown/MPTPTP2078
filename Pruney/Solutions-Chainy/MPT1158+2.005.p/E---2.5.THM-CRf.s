%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:52 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 687 expanded)
%              Number of clauses        :   46 ( 260 expanded)
%              Number of leaves         :    9 ( 163 expanded)
%              Depth                    :   15
%              Number of atoms          :  308 (4439 expanded)
%              Number of equality atoms :   47 ( 284 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_orders_2,conjecture,(
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
              <=> r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(fraenkel_a_2_1_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

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
                <=> r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_orders_2])).

fof(c_0_10,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | ~ m1_subset_1(X30,X29)
      | k6_domain_1(X29,X30) = k1_tarski(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_11,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X22,X23,X24,X26,X27] :
      ( ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X23))
        | ~ r2_hidden(X22,a_2_1_orders_2(X23,X24))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( X22 = esk2_3(X22,X23,X24)
        | ~ r2_hidden(X22,a_2_1_orders_2(X23,X24))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_hidden(X26,X24)
        | r2_orders_2(X23,esk2_3(X22,X23,X24),X26)
        | ~ r2_hidden(X22,a_2_1_orders_2(X23,X24))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( m1_subset_1(esk3_4(X22,X23,X24,X27),u1_struct_0(X23))
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | X22 != X27
        | r2_hidden(X22,a_2_1_orders_2(X23,X24))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( r2_hidden(esk3_4(X22,X23,X24,X27),X24)
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | X22 != X27
        | r2_hidden(X22,a_2_1_orders_2(X23,X24))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) )
      & ( ~ r2_orders_2(X23,X27,esk3_4(X22,X23,X24,X27))
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | X22 != X27
        | r2_hidden(X22,a_2_1_orders_2(X23,X24))
        | v2_struct_0(X23)
        | ~ v3_orders_2(X23)
        | ~ v4_orders_2(X23)
        | ~ v5_orders_2(X23)
        | ~ l1_orders_2(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_13,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X19)
      | m1_subset_1(k6_domain_1(X19,X20),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) )
    & ( r2_orders_2(esk4_0,esk5_0,esk6_0)
      | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ) ),
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
    | r2_hidden(X1,a_2_1_orders_2(X2,X3))
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
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k2_orders_2(X17,X18) = a_2_1_orders_2(X17,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

fof(c_0_22,plain,(
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

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk6_0) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,plain,
    ( r2_hidden(X3,a_2_1_orders_2(X1,X4))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != X2
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0),k2_tarski(esk6_0,esk6_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( k2_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)) = a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_44,plain,
    ( r2_orders_2(X2,esk2_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,plain,
    ( r2_orders_2(X1,esk2_3(X2,X1,k2_tarski(X3,X4)),X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tarski(X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,k2_tarski(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_35]),c_0_48])).

cnf(c_0_51,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_19]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_35])).

cnf(c_0_53,negated_conjecture,
    ( esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_50]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_57,plain,(
    ! [X16] :
      ( v2_struct_0(X16)
      | ~ l1_struct_0(X16)
      | ~ v1_xboole_0(u1_struct_0(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_43]),c_0_50])).

fof(c_0_61,plain,(
    ! [X21] :
      ( ~ l1_orders_2(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_62,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_29])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.028 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t52_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_orders_2)).
% 0.20/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.20/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.41  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.20/0.41  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.20/0.41  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 0.20/0.41  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.20/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.41  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.41  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)))))))), inference(assume_negation,[status(cth)],[t52_orders_2])).
% 0.20/0.41  fof(c_0_10, plain, ![X29, X30]:(v1_xboole_0(X29)|~m1_subset_1(X30,X29)|k6_domain_1(X29,X30)=k1_tarski(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.20/0.41  fof(c_0_11, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.41  fof(c_0_12, plain, ![X22, X23, X24, X26, X27]:((((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X23))|~r2_hidden(X22,a_2_1_orders_2(X23,X24))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))))&(X22=esk2_3(X22,X23,X24)|~r2_hidden(X22,a_2_1_orders_2(X23,X24))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))))))&(~m1_subset_1(X26,u1_struct_0(X23))|(~r2_hidden(X26,X24)|r2_orders_2(X23,esk2_3(X22,X23,X24),X26))|~r2_hidden(X22,a_2_1_orders_2(X23,X24))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23))))))&((m1_subset_1(esk3_4(X22,X23,X24,X27),u1_struct_0(X23))|(~m1_subset_1(X27,u1_struct_0(X23))|X22!=X27)|r2_hidden(X22,a_2_1_orders_2(X23,X24))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))))&((r2_hidden(esk3_4(X22,X23,X24,X27),X24)|(~m1_subset_1(X27,u1_struct_0(X23))|X22!=X27)|r2_hidden(X22,a_2_1_orders_2(X23,X24))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))))&(~r2_orders_2(X23,X27,esk3_4(X22,X23,X24,X27))|(~m1_subset_1(X27,u1_struct_0(X23))|X22!=X27)|r2_hidden(X22,a_2_1_orders_2(X23,X24))|(v2_struct_0(X23)|~v3_orders_2(X23)|~v4_orders_2(X23)|~v5_orders_2(X23)|~l1_orders_2(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.20/0.41  fof(c_0_13, plain, ![X19, X20]:(v1_xboole_0(X19)|~m1_subset_1(X20,X19)|m1_subset_1(k6_domain_1(X19,X20),k1_zfmisc_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.20/0.41  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))))&(r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.41  cnf(c_0_15, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.41  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_17, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_18, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.41  fof(c_0_21, plain, ![X17, X18]:(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k2_orders_2(X17,X18)=a_2_1_orders_2(X17,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.20/0.41  fof(c_0_22, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.20/0.41  cnf(c_0_23, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_26, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk6_0)=k2_tarski(esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_20, c_0_19])).
% 0.20/0.41  cnf(c_0_32, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.41  cnf(c_0_33, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.20/0.41  cnf(c_0_38, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_39, plain, (r2_hidden(X3,a_2_1_orders_2(X1,X4))|v2_struct_0(X1)|~r2_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))|~m1_subset_1(X2,u1_struct_0(X1))|X3!=X2|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_40, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0),k2_tarski(esk6_0,esk6_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.41  cnf(c_0_42, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,k2_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_36, c_0_31])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (k2_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))=a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_37, c_0_31])).
% 0.20/0.41  cnf(c_0_44, plain, (r2_orders_2(X2,esk2_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_45, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_38])])).
% 0.20/0.41  cnf(c_0_46, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_47, negated_conjecture, (esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0)=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.41  cnf(c_0_49, plain, (r2_orders_2(X1,esk2_3(X2,X1,k2_tarski(X3,X4)),X3)|v2_struct_0(X1)|~m1_subset_1(k2_tarski(X3,X4),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X2,a_2_1_orders_2(X1,k2_tarski(X3,X4)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_35]), c_0_48])).
% 0.20/0.41  cnf(c_0_51, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_19]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_35])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_50]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_35])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.41  fof(c_0_57, plain, ![X16]:(v2_struct_0(X16)|~l1_struct_0(X16)|~v1_xboole_0(u1_struct_0(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_56, c_0_31])).
% 0.20/0.41  cnf(c_0_59, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_43]), c_0_50])).
% 0.20/0.41  fof(c_0_61, plain, ![X21]:(~l1_orders_2(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_29])).
% 0.20/0.41  cnf(c_0_63, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_25])]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 65
% 0.20/0.41  # Proof object clause steps            : 46
% 0.20/0.41  # Proof object formula steps           : 19
% 0.20/0.41  # Proof object conjectures             : 31
% 0.20/0.41  # Proof object clause conjectures      : 28
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 21
% 0.20/0.41  # Proof object initial formulas used   : 9
% 0.20/0.41  # Proof object generating inferences   : 20
% 0.20/0.41  # Proof object simplifying inferences  : 46
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 9
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 27
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 26
% 0.20/0.41  # Processed clauses                    : 243
% 0.20/0.41  # ...of these trivial                  : 0
% 0.20/0.41  # ...subsumed                          : 62
% 0.20/0.41  # ...remaining for further processing  : 181
% 0.20/0.41  # Other redundant clauses eliminated   : 26
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 12
% 0.20/0.41  # Backward-rewritten                   : 99
% 0.20/0.41  # Generated clauses                    : 538
% 0.20/0.41  # ...of the previous two non-trivial   : 505
% 0.20/0.41  # Contextual simplify-reflections      : 9
% 0.20/0.41  # Paramodulations                      : 502
% 0.20/0.41  # Factorizations                       : 12
% 0.20/0.41  # Equation resolutions                 : 26
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 38
% 0.20/0.41  #    Positive orientable unit clauses  : 9
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 2
% 0.20/0.41  #    Non-unit-clauses                  : 27
% 0.20/0.41  # Current number of unprocessed clauses: 312
% 0.20/0.41  # ...number of literals in the above   : 1438
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 138
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 4270
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1018
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 83
% 0.20/0.41  # Unit Clause-clause subsumption calls : 10
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 3
% 0.20/0.41  # BW rewrite match successes           : 1
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 25184
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.053 s
% 0.20/0.41  # System time              : 0.007 s
% 0.20/0.41  # Total time               : 0.060 s
% 0.20/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
