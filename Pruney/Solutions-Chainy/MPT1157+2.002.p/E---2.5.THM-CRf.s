%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:51 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   78 (4243 expanded)
%              Number of clauses        :   59 (1443 expanded)
%              Number of leaves         :    9 (1019 expanded)
%              Depth                    :   19
%              Number of atoms          :  360 (30507 expanded)
%              Number of equality atoms :   47 ( 934 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k1_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

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
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | k6_domain_1(X30,X31) = k1_tarski(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_11,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_12,plain,(
    ! [X23,X24,X25,X27,X28] :
      ( ( m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X24))
        | ~ r2_hidden(X23,a_2_0_orders_2(X24,X25))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( X23 = esk2_3(X23,X24,X25)
        | ~ r2_hidden(X23,a_2_0_orders_2(X24,X25))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ r2_hidden(X27,X25)
        | r2_orders_2(X24,X27,esk2_3(X23,X24,X25))
        | ~ r2_hidden(X23,a_2_0_orders_2(X24,X25))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( m1_subset_1(esk3_4(X23,X24,X25,X28),u1_struct_0(X24))
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | X23 != X28
        | r2_hidden(X23,a_2_0_orders_2(X24,X25))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( r2_hidden(esk3_4(X23,X24,X25,X28),X25)
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | X23 != X28
        | r2_hidden(X23,a_2_0_orders_2(X24,X25))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( ~ r2_orders_2(X24,esk3_4(X23,X24,X25,X28),X28)
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | X23 != X28
        | r2_hidden(X23,a_2_0_orders_2(X24,X25))
        | v2_struct_0(X24)
        | ~ v3_orders_2(X24)
        | ~ v4_orders_2(X24)
        | ~ v5_orders_2(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_13,plain,(
    ! [X32,X33] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X32),X33),X32)
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X32),X33),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ l1_orders_2(X32) ) ) ),
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
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
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
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_34,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v3_orders_2(X19)
      | ~ v4_orders_2(X19)
      | ~ v5_orders_2(X19)
      | ~ l1_orders_2(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | k1_orders_2(X19,X20) = a_2_0_orders_2(X19,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_35,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_36,plain,
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

cnf(c_0_37,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0),k2_tarski(esk5_0,esk5_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk6_0),k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_29])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ r2_orders_2(X1,esk3_4(X2,X1,X3,X2),X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_29]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))
    | ~ r2_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_20]),c_0_27]),c_0_28]),c_0_21]),c_0_26])]),c_0_22]),c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29])).

fof(c_0_50,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ v3_orders_2(X21)
      | ~ v4_orders_2(X21)
      | ~ v5_orders_2(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(k1_orders_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_54,plain,
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

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_45]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_30])).

cnf(c_0_59,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,k2_tarski(X4,X2)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k2_tarski(X4,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,k2_tarski(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])).

cnf(c_0_61,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_62,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)))
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_20]),c_0_27]),c_0_28]),c_0_21]),c_0_19])]),c_0_22])).

cnf(c_0_63,negated_conjecture,
    ( esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)) = esk6_0
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_60]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)
    | r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_19]),c_0_20]),c_0_27]),c_0_28]),c_0_21])]),c_0_22])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_66,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_33])).

cnf(c_0_67,negated_conjecture,
    ( esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_33])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_45])).

cnf(c_0_70,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_60])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_57]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:42:51 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.42  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.42  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.42  #
% 0.18/0.42  # Preprocessing time       : 0.028 s
% 0.18/0.42  # Presaturation interreduction done
% 0.18/0.42  
% 0.18/0.42  # Proof found!
% 0.18/0.42  # SZS status Theorem
% 0.18/0.42  # SZS output start CNFRefutation
% 0.18/0.42  fof(t51_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_orders_2)).
% 0.18/0.42  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.18/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.42  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.18/0.42  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 0.18/0.42  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.42  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 0.18/0.42  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.18/0.42  fof(dt_k1_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 0.18/0.42  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))))), inference(assume_negation,[status(cth)],[t51_orders_2])).
% 0.18/0.42  fof(c_0_10, plain, ![X30, X31]:(v1_xboole_0(X30)|~m1_subset_1(X31,X30)|k6_domain_1(X30,X31)=k1_tarski(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.18/0.42  fof(c_0_11, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.42  fof(c_0_12, plain, ![X23, X24, X25, X27, X28]:((((m1_subset_1(esk2_3(X23,X24,X25),u1_struct_0(X24))|~r2_hidden(X23,a_2_0_orders_2(X24,X25))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))&(X23=esk2_3(X23,X24,X25)|~r2_hidden(X23,a_2_0_orders_2(X24,X25))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))))))&(~m1_subset_1(X27,u1_struct_0(X24))|(~r2_hidden(X27,X25)|r2_orders_2(X24,X27,esk2_3(X23,X24,X25)))|~r2_hidden(X23,a_2_0_orders_2(X24,X25))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))))))&((m1_subset_1(esk3_4(X23,X24,X25,X28),u1_struct_0(X24))|(~m1_subset_1(X28,u1_struct_0(X24))|X23!=X28)|r2_hidden(X23,a_2_0_orders_2(X24,X25))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))&((r2_hidden(esk3_4(X23,X24,X25,X28),X25)|(~m1_subset_1(X28,u1_struct_0(X24))|X23!=X28)|r2_hidden(X23,a_2_0_orders_2(X24,X25))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))&(~r2_orders_2(X24,esk3_4(X23,X24,X25,X28),X28)|(~m1_subset_1(X28,u1_struct_0(X24))|X23!=X28)|r2_hidden(X23,a_2_0_orders_2(X24,X25))|(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.18/0.42  fof(c_0_13, plain, ![X32, X33]:((v6_orders_2(k6_domain_1(u1_struct_0(X32),X33),X32)|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v3_orders_2(X32)|~l1_orders_2(X32)))&(m1_subset_1(k6_domain_1(u1_struct_0(X32),X33),k1_zfmisc_1(u1_struct_0(X32)))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v3_orders_2(X32)|~l1_orders_2(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.18/0.42  fof(c_0_14, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))))&(r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.18/0.42  cnf(c_0_15, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.42  cnf(c_0_16, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.42  cnf(c_0_17, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_0_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_18, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.18/0.42  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_21, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_23, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.42  fof(c_0_24, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.42  cnf(c_0_25, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_17])).
% 0.18/0.42  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_27, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_28, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_29, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])]), c_0_22])).
% 0.18/0.42  cnf(c_0_30, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.18/0.42  cnf(c_0_31, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.42  cnf(c_0_32, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk4_0,X1,esk6_0),X1)|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.18/0.42  cnf(c_0_33, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.42  fof(c_0_34, plain, ![X19, X20]:(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|k1_orders_2(X19,X20)=a_2_0_orders_2(X19,X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.18/0.42  fof(c_0_35, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|~v1_xboole_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.18/0.42  cnf(c_0_36, plain, (r2_hidden(X2,a_2_0_orders_2(X1,X3))|v2_struct_0(X1)|~r2_orders_2(X1,esk3_4(X2,X1,X3,X4),X4)|~m1_subset_1(X4,u1_struct_0(X1))|X2!=X4|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_37, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.18/0.42  cnf(c_0_38, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0),k2_tarski(esk5_0,esk5_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.18/0.42  cnf(c_0_39, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.42  cnf(c_0_40, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.18/0.42  cnf(c_0_41, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk6_0),k6_domain_1(u1_struct_0(esk4_0),esk5_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_32, c_0_29])).
% 0.18/0.42  cnf(c_0_42, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~r2_orders_2(X1,esk3_4(X2,X1,X3,X2),X2)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_36])).
% 0.18/0.42  cnf(c_0_43, negated_conjecture, (esk3_4(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0),esk6_0)=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.42  cnf(c_0_44, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_45, negated_conjecture, (k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_29]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.18/0.42  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v1_xboole_0(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.18/0.42  cnf(c_0_47, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))|~r2_orders_2(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_20]), c_0_27]), c_0_28]), c_0_21]), c_0_26])]), c_0_22]), c_0_33])).
% 0.18/0.42  cnf(c_0_48, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.18/0.42  cnf(c_0_49, negated_conjecture, (r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_29])).
% 0.18/0.42  fof(c_0_50, plain, ![X21, X22]:(v2_struct_0(X21)|~v3_orders_2(X21)|~v4_orders_2(X21)|~v5_orders_2(X21)|~l1_orders_2(X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|m1_subset_1(k1_orders_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_orders_2])])])).
% 0.18/0.42  cnf(c_0_51, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.42  cnf(c_0_52, negated_conjecture, (r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])).
% 0.18/0.42  cnf(c_0_53, plain, (v2_struct_0(X1)|m1_subset_1(k1_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.18/0.42  cnf(c_0_54, plain, (r2_orders_2(X2,X1,esk2_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_55, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_51])])).
% 0.18/0.42  cnf(c_0_56, negated_conjecture, (r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))|~v1_xboole_0(X1)|~m1_subset_1(a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.18/0.42  cnf(c_0_57, negated_conjecture, (m1_subset_1(a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_45]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.18/0.42  cnf(c_0_58, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(spm,[status(thm)],[c_0_52, c_0_30])).
% 0.18/0.42  cnf(c_0_59, plain, (r2_orders_2(X1,X2,esk2_3(X3,X1,k2_tarski(X4,X2)))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k2_tarski(X4,X2),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X3,a_2_0_orders_2(X1,k2_tarski(X4,X2)))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.42  cnf(c_0_60, negated_conjecture, (r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k2_tarski(esk5_0,esk5_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_58])).
% 0.18/0.42  cnf(c_0_61, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.42  cnf(c_0_62, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)))|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_20]), c_0_27]), c_0_28]), c_0_21]), c_0_19])]), c_0_22])).
% 0.18/0.42  cnf(c_0_63, negated_conjecture, (esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0))=esk6_0|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_60]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.18/0.42  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)|r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_19]), c_0_20]), c_0_27]), c_0_28]), c_0_21])]), c_0_22])).
% 0.18/0.42  cnf(c_0_65, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.42  cnf(c_0_66, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0)))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_62, c_0_33])).
% 0.18/0.42  cnf(c_0_67, negated_conjecture, (esk2_3(esk6_0,esk4_0,k2_tarski(esk5_0,esk5_0))=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_63, c_0_33])).
% 0.18/0.42  cnf(c_0_68, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk5_0))|r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_64, c_0_29])).
% 0.18/0.42  cnf(c_0_69, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(rw,[status(thm)],[c_0_65, c_0_45])).
% 0.18/0.42  cnf(c_0_70, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.42  cnf(c_0_71, negated_conjecture, (r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v1_xboole_0(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 0.18/0.42  cnf(c_0_72, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.18/0.42  cnf(c_0_73, negated_conjecture, (r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_71, c_0_29])).
% 0.18/0.42  cnf(c_0_74, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_60])])).
% 0.18/0.42  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_0,a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_74])])).
% 0.18/0.42  cnf(c_0_76, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_40, c_0_75])).
% 0.18/0.42  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_57]), c_0_74])]), ['proof']).
% 0.18/0.42  # SZS output end CNFRefutation
% 0.18/0.42  # Proof object total steps             : 78
% 0.18/0.42  # Proof object clause steps            : 59
% 0.18/0.42  # Proof object formula steps           : 19
% 0.18/0.42  # Proof object conjectures             : 44
% 0.18/0.42  # Proof object clause conjectures      : 41
% 0.18/0.42  # Proof object formula conjectures     : 3
% 0.18/0.42  # Proof object initial clauses used    : 21
% 0.18/0.42  # Proof object initial formulas used   : 9
% 0.18/0.42  # Proof object generating inferences   : 30
% 0.18/0.42  # Proof object simplifying inferences  : 66
% 0.18/0.42  # Training examples: 0 positive, 0 negative
% 0.18/0.42  # Parsed axioms                        : 9
% 0.18/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.42  # Initial clauses                      : 28
% 0.18/0.42  # Removed in clause preprocessing      : 1
% 0.18/0.42  # Initial clauses in saturation        : 27
% 0.18/0.42  # Processed clauses                    : 427
% 0.18/0.42  # ...of these trivial                  : 3
% 0.18/0.42  # ...subsumed                          : 100
% 0.18/0.42  # ...remaining for further processing  : 324
% 0.18/0.42  # Other redundant clauses eliminated   : 26
% 0.18/0.42  # Clauses deleted for lack of memory   : 0
% 0.18/0.42  # Backward-subsumed                    : 6
% 0.18/0.42  # Backward-rewritten                   : 204
% 0.18/0.42  # Generated clauses                    : 1847
% 0.18/0.42  # ...of the previous two non-trivial   : 1742
% 0.18/0.42  # Contextual simplify-reflections      : 4
% 0.18/0.42  # Paramodulations                      : 1811
% 0.18/0.42  # Factorizations                       : 12
% 0.18/0.42  # Equation resolutions                 : 26
% 0.18/0.42  # Propositional unsat checks           : 0
% 0.18/0.42  #    Propositional check models        : 0
% 0.18/0.42  #    Propositional check unsatisfiable : 0
% 0.18/0.42  #    Propositional clauses             : 0
% 0.18/0.42  #    Propositional clauses after purity: 0
% 0.18/0.42  #    Propositional unsat core size     : 0
% 0.18/0.42  #    Propositional preprocessing time  : 0.000
% 0.18/0.42  #    Propositional encoding time       : 0.000
% 0.18/0.42  #    Propositional solver time         : 0.000
% 0.18/0.42  #    Success case prop preproc time    : 0.000
% 0.18/0.42  #    Success case prop encoding time   : 0.000
% 0.18/0.42  #    Success case prop solver time     : 0.000
% 0.18/0.42  # Current number of processed clauses  : 81
% 0.18/0.42  #    Positive orientable unit clauses  : 37
% 0.18/0.42  #    Positive unorientable unit clauses: 0
% 0.18/0.42  #    Negative unit clauses             : 2
% 0.18/0.42  #    Non-unit-clauses                  : 42
% 0.18/0.42  # Current number of unprocessed clauses: 1341
% 0.18/0.42  # ...number of literals in the above   : 4351
% 0.18/0.42  # Current number of archived formulas  : 0
% 0.18/0.42  # Current number of archived clauses   : 238
% 0.18/0.42  # Clause-clause subsumption calls (NU) : 5291
% 0.18/0.42  # Rec. Clause-clause subsumption calls : 4512
% 0.18/0.42  # Non-unit clause-clause subsumptions  : 109
% 0.18/0.42  # Unit Clause-clause subsumption calls : 322
% 0.18/0.42  # Rewrite failures with RHS unbound    : 0
% 0.18/0.42  # BW rewrite match attempts            : 130
% 0.18/0.42  # BW rewrite match successes           : 11
% 0.18/0.42  # Condensation attempts                : 0
% 0.18/0.42  # Condensation successes               : 0
% 0.18/0.42  # Termbank termtop insertions          : 87537
% 0.18/0.42  
% 0.18/0.42  # -------------------------------------------------
% 0.18/0.42  # User time                : 0.083 s
% 0.18/0.42  # System time              : 0.009 s
% 0.18/0.42  # Total time               : 0.092 s
% 0.18/0.42  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
