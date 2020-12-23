%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:52 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   69 (1266 expanded)
%              Number of clauses        :   50 ( 413 expanded)
%              Number of leaves         :    9 ( 307 expanded)
%              Depth                    :   15
%              Number of atoms          :  323 (9281 expanded)
%              Number of equality atoms :   43 ( 216 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(t50_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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
    ! [X28,X29] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X28),X29),X28)
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v3_orders_2(X28)
        | ~ l1_orders_2(X28) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X28),X29),k1_zfmisc_1(u1_struct_0(X28)))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | v2_struct_0(X28)
        | ~ v3_orders_2(X28)
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

fof(c_0_11,negated_conjecture,
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

fof(c_0_12,plain,(
    ! [X19,X20,X21,X23,X24] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( X19 = esk2_3(X19,X20,X21)
        | ~ r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X23,X21)
        | r2_orders_2(X20,esk2_3(X19,X20,X21),X23)
        | ~ r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( m1_subset_1(esk3_4(X19,X20,X21,X24),u1_struct_0(X20))
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r2_hidden(esk3_4(X19,X20,X21,X24),X21)
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ r2_orders_2(X20,X24,esk3_4(X19,X20,X21,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | k2_orders_2(X17,X18) = a_2_1_orders_2(X17,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
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

fof(c_0_20,plain,(
    ! [X30,X31] :
      ( v2_struct_0(X30)
      | ~ v3_orders_2(X30)
      | ~ v4_orders_2(X30)
      | ~ v5_orders_2(X30)
      | ~ l1_orders_2(X30)
      | ~ m1_subset_1(X31,u1_struct_0(X30))
      | ~ r2_hidden(X31,k2_orders_2(X30,k6_domain_1(u1_struct_0(X30),X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_orders_2])])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16]),c_0_23]),c_0_24]),c_0_17])]),c_0_18])).

fof(c_0_28,plain,(
    ! [X26,X27] :
      ( v1_xboole_0(X26)
      | ~ m1_subset_1(X27,X26)
      | k6_domain_1(X26,X27) = k1_tarski(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_30,plain,(
    ! [X14,X15,X16] :
      ( ~ r2_hidden(X14,X15)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X16))
      | ~ v1_xboole_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk4_0,X1,esk6_0),X1)
    | r2_hidden(esk6_0,a_2_1_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_16]),c_0_23]),c_0_24]),c_0_17])]),c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(esk6_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16]),c_0_23]),c_0_24]),c_0_17]),c_0_15])]),c_0_18])).

fof(c_0_33,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk6_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_22]),c_0_32])).

cnf(c_0_38,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k2_tarski(esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk4_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_47,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k2_tarski(esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk4_0),esk6_0) ),
    inference(sr,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_45]),c_0_16]),c_0_23]),c_0_24]),c_0_17])]),c_0_18])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).

cnf(c_0_51,plain,
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

cnf(c_0_52,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_22])).

cnf(c_0_54,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) = esk6_0
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_27])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,plain,
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

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_62,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_16]),c_0_23]),c_0_24]),c_0_17]),c_0_22]),c_0_45])]),c_0_18]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( r2_orders_2(X1,esk2_3(X2,X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk6_0)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( esk2_3(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = esk5_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_16]),c_0_23]),c_0_24]),c_0_17]),c_0_22])]),c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_63])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_63]),c_0_66]),c_0_16]),c_0_23]),c_0_24]),c_0_17]),c_0_22]),c_0_15])]),c_0_67]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.14/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.029 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t52_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_orders_2)).
% 0.14/0.38  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 0.14/0.38  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.14/0.38  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 0.14/0.38  fof(t50_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_orders_2)).
% 0.14/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.14/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)))))))), inference(assume_negation,[status(cth)],[t52_orders_2])).
% 0.14/0.38  fof(c_0_10, plain, ![X28, X29]:((v6_orders_2(k6_domain_1(u1_struct_0(X28),X29),X28)|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v3_orders_2(X28)|~l1_orders_2(X28)))&(m1_subset_1(k6_domain_1(u1_struct_0(X28),X29),k1_zfmisc_1(u1_struct_0(X28)))|~m1_subset_1(X29,u1_struct_0(X28))|(v2_struct_0(X28)|~v3_orders_2(X28)|~l1_orders_2(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.14/0.38  fof(c_0_11, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))))&(r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X19, X20, X21, X23, X24]:((((m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X20))|~r2_hidden(X19,a_2_1_orders_2(X20,X21))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))&(X19=esk2_3(X19,X20,X21)|~r2_hidden(X19,a_2_1_orders_2(X20,X21))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))))))&(~m1_subset_1(X23,u1_struct_0(X20))|(~r2_hidden(X23,X21)|r2_orders_2(X20,esk2_3(X19,X20,X21),X23))|~r2_hidden(X19,a_2_1_orders_2(X20,X21))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))))))&((m1_subset_1(esk3_4(X19,X20,X21,X24),u1_struct_0(X20))|(~m1_subset_1(X24,u1_struct_0(X20))|X19!=X24)|r2_hidden(X19,a_2_1_orders_2(X20,X21))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))&((r2_hidden(esk3_4(X19,X20,X21,X24),X21)|(~m1_subset_1(X24,u1_struct_0(X20))|X19!=X24)|r2_hidden(X19,a_2_1_orders_2(X20,X21))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))&(~r2_orders_2(X20,X24,esk3_4(X19,X20,X21,X24))|(~m1_subset_1(X24,u1_struct_0(X20))|X19!=X24)|r2_hidden(X19,a_2_1_orders_2(X20,X21))|(v2_struct_0(X20)|~v3_orders_2(X20)|~v4_orders_2(X20)|~v5_orders_2(X20)|~l1_orders_2(X20)|~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X17, X18]:(v2_struct_0(X17)|~v3_orders_2(X17)|~v4_orders_2(X17)|~v5_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|k2_orders_2(X17,X18)=a_2_1_orders_2(X17,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.14/0.38  cnf(c_0_14, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  fof(c_0_20, plain, ![X30, X31]:(v2_struct_0(X30)|~v3_orders_2(X30)|~v4_orders_2(X30)|~v5_orders_2(X30)|~l1_orders_2(X30)|(~m1_subset_1(X31,u1_struct_0(X30))|~r2_hidden(X31,k2_orders_2(X30,k6_domain_1(u1_struct_0(X30),X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t50_orders_2])])])])).
% 0.14/0.38  cnf(c_0_21, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16]), c_0_23]), c_0_24]), c_0_17])]), c_0_18])).
% 0.14/0.38  fof(c_0_28, plain, ![X26, X27]:(v1_xboole_0(X26)|~m1_subset_1(X27,X26)|k6_domain_1(X26,X27)=k1_tarski(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.38  fof(c_0_29, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.38  fof(c_0_30, plain, ![X14, X15, X16]:(~r2_hidden(X14,X15)|~m1_subset_1(X15,k1_zfmisc_1(X16))|~v1_xboole_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk4_0,X1,esk6_0),X1)|r2_hidden(esk6_0,a_2_1_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_16]), c_0_23]), c_0_24]), c_0_17])]), c_0_18])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (~r2_hidden(esk6_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16]), c_0_23]), c_0_24]), c_0_17]), c_0_15])]), c_0_18])).
% 0.14/0.38  fof(c_0_33, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_34, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_35, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(esk3_4(esk6_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk6_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_22]), c_0_32])).
% 0.14/0.38  cnf(c_0_38, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_39, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.38  cnf(c_0_41, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_42, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_38, c_0_35])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (k2_tarski(esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk4_0),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_39, c_0_15])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_46, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_41, c_0_35])).
% 0.14/0.38  cnf(c_0_47, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (k2_tarski(esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk4_0),esk6_0)), inference(sr,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_45]), c_0_16]), c_0_23]), c_0_24]), c_0_17])]), c_0_18])).
% 0.14/0.38  cnf(c_0_50, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_46])])).
% 0.14/0.38  cnf(c_0_51, plain, (r2_hidden(X3,a_2_1_orders_2(X1,X4))|v2_struct_0(X1)|~r2_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))|~m1_subset_1(X2,u1_struct_0(X1))|X3!=X2|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (X1=esk6_0|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_49, c_0_22])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 0.14/0.38  cnf(c_0_56, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_51])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)=esk6_0|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(rw,[status(thm)],[c_0_54, c_0_27])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_60, plain, (r2_orders_2(X2,esk2_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (r2_hidden(esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[c_0_55, c_0_44])).
% 0.14/0.38  cnf(c_0_62, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_63, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_16]), c_0_23]), c_0_24]), c_0_17]), c_0_22]), c_0_45])]), c_0_18]), c_0_58])).
% 0.14/0.38  cnf(c_0_64, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(rw,[status(thm)],[c_0_59, c_0_27])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (r2_orders_2(X1,esk2_3(X2,X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk6_0)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk6_0,u1_struct_0(X1))|~r2_hidden(X2,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, (esk2_3(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=esk5_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_16]), c_0_23]), c_0_24]), c_0_17]), c_0_22])]), c_0_18])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_63])])).
% 0.14/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_63]), c_0_66]), c_0_16]), c_0_23]), c_0_24]), c_0_17]), c_0_22]), c_0_15])]), c_0_67]), c_0_18]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 69
% 0.14/0.38  # Proof object clause steps            : 50
% 0.14/0.38  # Proof object formula steps           : 19
% 0.14/0.38  # Proof object conjectures             : 34
% 0.14/0.38  # Proof object clause conjectures      : 31
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 21
% 0.14/0.38  # Proof object initial formulas used   : 9
% 0.14/0.38  # Proof object generating inferences   : 17
% 0.14/0.38  # Proof object simplifying inferences  : 70
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 9
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 26
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 25
% 0.14/0.38  # Processed clauses                    : 132
% 0.14/0.38  # ...of these trivial                  : 2
% 0.14/0.38  # ...subsumed                          : 10
% 0.14/0.38  # ...remaining for further processing  : 120
% 0.14/0.38  # Other redundant clauses eliminated   : 9
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 4
% 0.14/0.38  # Backward-rewritten                   : 9
% 0.14/0.38  # Generated clauses                    : 142
% 0.14/0.38  # ...of the previous two non-trivial   : 125
% 0.14/0.38  # Contextual simplify-reflections      : 1
% 0.14/0.38  # Paramodulations                      : 127
% 0.14/0.38  # Factorizations                       : 2
% 0.14/0.38  # Equation resolutions                 : 9
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
% 0.14/0.38  # Current number of processed clauses  : 72
% 0.14/0.38  #    Positive orientable unit clauses  : 21
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 7
% 0.14/0.38  #    Non-unit-clauses                  : 44
% 0.14/0.38  # Current number of unprocessed clauses: 38
% 0.14/0.38  # ...number of literals in the above   : 204
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 44
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 767
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 181
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.14/0.38  # Unit Clause-clause subsumption calls : 63
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 8
% 0.14/0.38  # BW rewrite match successes           : 4
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 6512
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.006 s
% 0.14/0.38  # Total time               : 0.042 s
% 0.14/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
