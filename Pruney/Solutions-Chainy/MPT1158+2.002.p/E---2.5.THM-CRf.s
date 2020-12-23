%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:52 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 691 expanded)
%              Number of clauses        :   46 ( 232 expanded)
%              Number of leaves         :    9 ( 167 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 (5036 expanded)
%              Number of equality atoms :   42 ( 173 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

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

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X13] : k2_tarski(X13,X13) = k1_tarski(X13) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_11,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X18,X19,X20,X22,X23] :
      ( ( m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X19))
        | ~ r2_hidden(X18,a_2_1_orders_2(X19,X20))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( X18 = esk2_3(X18,X19,X20)
        | ~ r2_hidden(X18,a_2_1_orders_2(X19,X20))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ r2_hidden(X22,X20)
        | r2_orders_2(X19,esk2_3(X18,X19,X20),X22)
        | ~ r2_hidden(X18,a_2_1_orders_2(X19,X20))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( m1_subset_1(esk3_4(X18,X19,X20,X23),u1_struct_0(X19))
        | ~ m1_subset_1(X23,u1_struct_0(X19))
        | X18 != X23
        | r2_hidden(X18,a_2_1_orders_2(X19,X20))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( r2_hidden(esk3_4(X18,X19,X20,X23),X20)
        | ~ m1_subset_1(X23,u1_struct_0(X19))
        | X18 != X23
        | r2_hidden(X18,a_2_1_orders_2(X19,X20))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( ~ r2_orders_2(X19,X23,esk3_4(X18,X19,X20,X23))
        | ~ m1_subset_1(X23,u1_struct_0(X19))
        | X18 != X23
        | r2_hidden(X18,a_2_1_orders_2(X19,X20))
        | v2_struct_0(X19)
        | ~ v3_orders_2(X19)
        | ~ v4_orders_2(X19)
        | ~ v5_orders_2(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

cnf(c_0_14,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X27,X28] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X27),X28),X27)
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X27),X28),k1_zfmisc_1(u1_struct_0(X27)))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_32,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v3_orders_2(X15)
      | ~ v4_orders_2(X15)
      | ~ v5_orders_2(X15)
      | ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | k2_orders_2(X15,X16) = a_2_1_orders_2(X15,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_15])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( k2_tarski(esk6_0,esk6_0) = k6_domain_1(u1_struct_0(esk4_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_26]),c_0_29])]),c_0_30])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_37]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_45,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_35])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r2_orders_2(X1,esk2_3(X2,X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_37]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_49])).

cnf(c_0_52,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_54,negated_conjecture,
    ( r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_37]),c_0_23]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( esk2_3(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_37]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

fof(c_0_56,plain,(
    ! [X14] :
      ( v2_struct_0(X14)
      | ~ l1_struct_0(X14)
      | ~ v1_xboole_0(u1_struct_0(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(rw,[status(thm)],[c_0_53,c_0_44])).

cnf(c_0_58,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_51])).

fof(c_0_61,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_62,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_30])).

cnf(c_0_63,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.14/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.14/0.41  #
% 0.14/0.41  # Preprocessing time       : 0.039 s
% 0.14/0.41  # Presaturation interreduction done
% 0.14/0.41  
% 0.14/0.41  # Proof found!
% 0.14/0.41  # SZS status Theorem
% 0.14/0.41  # SZS output start CNFRefutation
% 0.14/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.14/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.14/0.41  fof(t52_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_orders_2)).
% 0.14/0.41  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.14/0.41  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 0.14/0.41  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 0.14/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.14/0.41  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.41  fof(c_0_9, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.14/0.41  fof(c_0_10, plain, ![X13]:k2_tarski(X13,X13)=k1_tarski(X13), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.41  fof(c_0_11, plain, ![X25, X26]:(v1_xboole_0(X25)|~m1_subset_1(X26,X25)|k6_domain_1(X25,X26)=k1_tarski(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.14/0.41  fof(c_0_12, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)))))))), inference(assume_negation,[status(cth)],[t52_orders_2])).
% 0.14/0.41  fof(c_0_13, plain, ![X18, X19, X20, X22, X23]:((((m1_subset_1(esk2_3(X18,X19,X20),u1_struct_0(X19))|~r2_hidden(X18,a_2_1_orders_2(X19,X20))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))))&(X18=esk2_3(X18,X19,X20)|~r2_hidden(X18,a_2_1_orders_2(X19,X20))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))))))&(~m1_subset_1(X22,u1_struct_0(X19))|(~r2_hidden(X22,X20)|r2_orders_2(X19,esk2_3(X18,X19,X20),X22))|~r2_hidden(X18,a_2_1_orders_2(X19,X20))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))))))&((m1_subset_1(esk3_4(X18,X19,X20,X23),u1_struct_0(X19))|(~m1_subset_1(X23,u1_struct_0(X19))|X18!=X23)|r2_hidden(X18,a_2_1_orders_2(X19,X20))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))))&((r2_hidden(esk3_4(X18,X19,X20,X23),X20)|(~m1_subset_1(X23,u1_struct_0(X19))|X18!=X23)|r2_hidden(X18,a_2_1_orders_2(X19,X20))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))))&(~r2_orders_2(X19,X23,esk3_4(X18,X19,X20,X23))|(~m1_subset_1(X23,u1_struct_0(X19))|X18!=X23)|r2_hidden(X18,a_2_1_orders_2(X19,X20))|(v2_struct_0(X19)|~v3_orders_2(X19)|~v4_orders_2(X19)|~v5_orders_2(X19)|~l1_orders_2(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.14/0.41  cnf(c_0_14, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.41  cnf(c_0_15, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.41  cnf(c_0_16, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.41  fof(c_0_17, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))))&(r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.14/0.41  cnf(c_0_18, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.41  fof(c_0_19, plain, ![X27, X28]:((v6_orders_2(k6_domain_1(u1_struct_0(X27),X28),X27)|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v3_orders_2(X27)|~l1_orders_2(X27)))&(m1_subset_1(k6_domain_1(u1_struct_0(X27),X28),k1_zfmisc_1(u1_struct_0(X27)))|~m1_subset_1(X28,u1_struct_0(X27))|(v2_struct_0(X27)|~v3_orders_2(X27)|~l1_orders_2(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.14/0.41  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.41  cnf(c_0_21, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.14/0.41  cnf(c_0_22, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_16, c_0_15])).
% 0.14/0.41  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_24, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_18])).
% 0.14/0.41  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_26, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_27, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_28, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_29, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_31, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.41  fof(c_0_32, plain, ![X15, X16]:(v2_struct_0(X15)|~v3_orders_2(X15)|~v4_orders_2(X15)|~v5_orders_2(X15)|~l1_orders_2(X15)|(~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|k2_orders_2(X15,X16)=a_2_1_orders_2(X15,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.14/0.41  cnf(c_0_33, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_20, c_0_15])).
% 0.14/0.41  cnf(c_0_34, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.14/0.41  cnf(c_0_35, negated_conjecture, (k2_tarski(esk6_0,esk6_0)=k6_domain_1(u1_struct_0(esk4_0),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.41  cnf(c_0_36, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.14/0.41  cnf(c_0_37, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_26]), c_0_29])]), c_0_30])).
% 0.14/0.41  cnf(c_0_38, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.41  cnf(c_0_39, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 0.14/0.41  cnf(c_0_40, plain, (r2_hidden(X3,a_2_1_orders_2(X1,X4))|v2_struct_0(X1)|~r2_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))|~m1_subset_1(X2,u1_struct_0(X1))|X3!=X2|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.41  cnf(c_0_41, negated_conjecture, (X1=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.41  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.41  cnf(c_0_43, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_44, negated_conjecture, (k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_37]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.14/0.41  cnf(c_0_45, plain, (r2_orders_2(X2,esk2_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.41  cnf(c_0_46, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk6_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(spm,[status(thm)],[c_0_39, c_0_35])).
% 0.14/0.41  cnf(c_0_47, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)), inference(er,[status(thm)],[c_0_40])).
% 0.14/0.41  cnf(c_0_48, negated_conjecture, (esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0)=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.41  cnf(c_0_49, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.41  cnf(c_0_50, negated_conjecture, (r2_orders_2(X1,esk2_3(X2,X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk6_0,u1_struct_0(X1))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~r2_hidden(X2,a_2_1_orders_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.41  cnf(c_0_51, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_37]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_49])).
% 0.14/0.41  cnf(c_0_52, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.41  cnf(c_0_53, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.41  cnf(c_0_54, negated_conjecture, (r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_37]), c_0_23]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.14/0.41  cnf(c_0_55, negated_conjecture, (esk2_3(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_51]), c_0_37]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.14/0.41  fof(c_0_56, plain, ![X14]:(v2_struct_0(X14)|~l1_struct_0(X14)|~v1_xboole_0(u1_struct_0(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.14/0.41  cnf(c_0_57, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(rw,[status(thm)],[c_0_53, c_0_44])).
% 0.14/0.41  cnf(c_0_58, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.41  cnf(c_0_59, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.41  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_51])).
% 0.14/0.41  fof(c_0_61, plain, ![X17]:(~l1_orders_2(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.41  cnf(c_0_62, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_30])).
% 0.14/0.41  cnf(c_0_63, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.14/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_26])]), ['proof']).
% 0.14/0.41  # SZS output end CNFRefutation
% 0.14/0.41  # Proof object total steps             : 65
% 0.14/0.41  # Proof object clause steps            : 46
% 0.14/0.41  # Proof object formula steps           : 19
% 0.14/0.41  # Proof object conjectures             : 30
% 0.14/0.41  # Proof object clause conjectures      : 27
% 0.14/0.41  # Proof object formula conjectures     : 3
% 0.14/0.41  # Proof object initial clauses used    : 21
% 0.14/0.41  # Proof object initial formulas used   : 9
% 0.14/0.41  # Proof object generating inferences   : 16
% 0.14/0.41  # Proof object simplifying inferences  : 54
% 0.14/0.41  # Training examples: 0 positive, 0 negative
% 0.14/0.41  # Parsed axioms                        : 9
% 0.14/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.41  # Initial clauses                      : 26
% 0.14/0.41  # Removed in clause preprocessing      : 1
% 0.14/0.41  # Initial clauses in saturation        : 25
% 0.14/0.41  # Processed clauses                    : 132
% 0.14/0.41  # ...of these trivial                  : 0
% 0.14/0.41  # ...subsumed                          : 11
% 0.14/0.41  # ...remaining for further processing  : 121
% 0.14/0.41  # Other redundant clauses eliminated   : 12
% 0.14/0.41  # Clauses deleted for lack of memory   : 0
% 0.14/0.41  # Backward-subsumed                    : 1
% 0.14/0.41  # Backward-rewritten                   : 28
% 0.14/0.41  # Generated clauses                    : 194
% 0.14/0.41  # ...of the previous two non-trivial   : 170
% 0.14/0.41  # Contextual simplify-reflections      : 2
% 0.14/0.41  # Paramodulations                      : 179
% 0.14/0.41  # Factorizations                       : 4
% 0.14/0.41  # Equation resolutions                 : 12
% 0.14/0.41  # Propositional unsat checks           : 0
% 0.14/0.41  #    Propositional check models        : 0
% 0.14/0.41  #    Propositional check unsatisfiable : 0
% 0.14/0.41  #    Propositional clauses             : 0
% 0.14/0.41  #    Propositional clauses after purity: 0
% 0.14/0.41  #    Propositional unsat core size     : 0
% 0.14/0.41  #    Propositional preprocessing time  : 0.000
% 0.14/0.41  #    Propositional encoding time       : 0.000
% 0.14/0.41  #    Propositional solver time         : 0.000
% 0.14/0.41  #    Success case prop preproc time    : 0.000
% 0.14/0.41  #    Success case prop encoding time   : 0.000
% 0.14/0.41  #    Success case prop solver time     : 0.000
% 0.14/0.41  # Current number of processed clauses  : 62
% 0.14/0.41  #    Positive orientable unit clauses  : 14
% 0.14/0.41  #    Positive unorientable unit clauses: 0
% 0.14/0.41  #    Negative unit clauses             : 2
% 0.14/0.41  #    Non-unit-clauses                  : 46
% 0.14/0.41  # Current number of unprocessed clauses: 87
% 0.14/0.41  # ...number of literals in the above   : 381
% 0.14/0.41  # Current number of archived formulas  : 0
% 0.14/0.41  # Current number of archived clauses   : 55
% 0.14/0.41  # Clause-clause subsumption calls (NU) : 1513
% 0.14/0.41  # Rec. Clause-clause subsumption calls : 323
% 0.14/0.41  # Non-unit clause-clause subsumptions  : 14
% 0.14/0.41  # Unit Clause-clause subsumption calls : 42
% 0.14/0.41  # Rewrite failures with RHS unbound    : 0
% 0.14/0.41  # BW rewrite match attempts            : 3
% 0.14/0.41  # BW rewrite match successes           : 2
% 0.14/0.41  # Condensation attempts                : 0
% 0.14/0.41  # Condensation successes               : 0
% 0.14/0.41  # Termbank termtop insertions          : 9227
% 0.14/0.41  
% 0.14/0.41  # -------------------------------------------------
% 0.14/0.41  # User time                : 0.050 s
% 0.14/0.41  # System time              : 0.005 s
% 0.14/0.41  # Total time               : 0.055 s
% 0.14/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
