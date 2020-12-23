%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1637+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:29 EST 2020

% Result     : Theorem 20.92s
% Output     : CNFRefutation 20.92s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 693 expanded)
%              Number of clauses        :   58 ( 287 expanded)
%              Number of leaves         :    9 ( 165 expanded)
%              Depth                    :   22
%              Number of atoms          :  294 (3177 expanded)
%              Number of equality atoms :   32 ( 483 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k5_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k5_waybel_0(X1,X2) = k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(fraenkel_a_2_0_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_waybel_0(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r1_orders_2(X2,X4,X5)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_waybel_0)).

fof(t14_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k3_waybel_0(X1,X2) = a_2_0_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_waybel_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k5_waybel_0(X1,X2))
                <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_waybel_0])).

fof(c_0_10,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_11,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,esk5_0))
      | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) )
    & ( r2_hidden(esk6_0,k5_waybel_0(esk4_0,esk5_0))
      | r1_orders_2(esk4_0,esk6_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_14,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | k5_waybel_0(X6,X7) = k3_waybel_0(X6,k6_domain_1(u1_struct_0(X6),X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_waybel_0])])])])).

cnf(c_0_16,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,esk5_0))
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k5_waybel_0(X1,X2) = k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_24,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_25,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,X1))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k3_waybel_0(X1,X2) = k5_waybel_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(k6_domain_1(u1_struct_0(X1),X3),k1_tarski(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_21]),c_0_23])).

cnf(c_0_31,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X26,X27] :
      ( v1_xboole_0(X26)
      | ~ m1_subset_1(X27,X26)
      | k6_domain_1(X26,X27) = k1_tarski(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(k6_domain_1(u1_struct_0(esk4_0),X1),k1_tarski(X2))
    | ~ r2_hidden(esk6_0,k3_waybel_0(esk4_0,X2))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_23]),c_0_28])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_27])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,k3_waybel_0(esk4_0,k6_domain_1(u1_struct_0(esk4_0),X1)))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_21])])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,k3_waybel_0(esk4_0,k1_tarski(X1)))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_36]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_38]),c_0_23])).

fof(c_0_41,plain,(
    ! [X19,X20,X21,X24,X25] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_0_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( X19 = esk2_3(X19,X20,X21)
        | ~ r2_hidden(X19,a_2_0_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_0_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r1_orders_2(X20,esk2_3(X19,X20,X21),esk3_3(X19,X20,X21))
        | ~ r2_hidden(X19,a_2_0_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r2_hidden(esk3_3(X19,X20,X21),X21)
        | ~ r2_hidden(X19,a_2_0_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | ~ m1_subset_1(X25,u1_struct_0(X20))
        | ~ r1_orders_2(X20,X24,X25)
        | ~ r2_hidden(X25,X21)
        | r2_hidden(X19,a_2_0_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_waybel_0])])])])])])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ l1_struct_0(esk4_0)
    | ~ r2_hidden(esk6_0,k3_waybel_0(esk4_0,k1_tarski(X1)))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_39]),c_0_23])).

fof(c_0_43,plain,(
    ! [X28,X29] :
      ( v2_struct_0(X28)
      | ~ l1_orders_2(X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | k3_waybel_0(X28,X29) = a_2_0_waybel_0(X28,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_waybel_0])])])])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_27])])).

cnf(c_0_45,plain,
    ( r2_hidden(X3,a_2_0_waybel_0(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,k3_waybel_0(esk4_0,k1_tarski(X1)))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_27])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k3_waybel_0(X1,X2) = a_2_0_waybel_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_19])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | v2_struct_0(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k1_tarski(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(esk6_0,a_2_0_waybel_0(esk4_0,k1_tarski(X1)))
    | ~ r2_hidden(esk5_0,k1_tarski(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_27])]),c_0_23]),c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,a_2_0_waybel_0(esk4_0,k1_tarski(esk5_0)))
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ r2_hidden(X2,k1_tarski(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_27])]),c_0_23]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk6_0,k5_waybel_0(esk4_0,esk5_0))
    | r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_orders_2(X1,esk6_0,X2)
    | ~ r2_hidden(esk6_0,a_2_0_waybel_0(X1,k1_tarski(X2)))
    | ~ r2_hidden(esk5_0,k1_tarski(X2))
    | ~ r2_hidden(esk4_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_19])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,a_2_0_waybel_0(esk4_0,k1_tarski(esk5_0)))
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(X1,esk6_0,esk5_0)
    | r2_hidden(esk6_0,k5_waybel_0(X1,esk5_0))
    | ~ r2_hidden(esk4_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_19])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_orders_2(X1,X2,X3)
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,k1_tarski(X3)))
    | ~ r2_hidden(esk5_0,k1_tarski(X3))
    | ~ r2_hidden(esk4_0,k1_tarski(X1))
    | ~ r2_hidden(esk6_0,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk6_0,a_2_0_waybel_0(esk4_0,k1_tarski(esk5_0)))
    | r2_hidden(esk6_0,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_34])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,k5_waybel_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_34]),c_0_34]),c_0_34])]),c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_60])])).

cnf(c_0_62,plain,
    ( r1_orders_2(X1,esk2_3(X2,X1,X3),esk3_3(X2,X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_63,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,esk6_0,X1)
    | ~ r2_hidden(X1,k1_tarski(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_19])).

cnf(c_0_65,plain,
    ( r1_orders_2(X1,X2,esk3_3(X2,X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_66,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(esk3_3(esk6_0,esk4_0,X1),k1_tarski(esk5_0))
    | ~ r2_hidden(esk6_0,a_2_0_waybel_0(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_27])]),c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk3_3(X1,esk4_0,X2),X2)
    | ~ r2_hidden(X1,a_2_0_waybel_0(esk4_0,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_66]),c_0_27])])).

cnf(c_0_69,plain,
    ( a_2_0_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = k5_waybel_0(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk6_0,a_2_0_waybel_0(esk4_0,k1_tarski(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_44])])).

cnf(c_0_71,plain,
    ( a_2_0_waybel_0(X1,X2) = k5_waybel_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(k6_domain_1(u1_struct_0(X1),X3),k1_tarski(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_19])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(k6_domain_1(u1_struct_0(esk4_0),X1),k1_tarski(k1_tarski(esk5_0)))
    | ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_44]),c_0_27])]),c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(k1_tarski(X1),k1_tarski(k1_tarski(esk5_0)))
    | ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ r2_hidden(k1_tarski(X1),k1_tarski(k1_tarski(esk5_0)))
    | ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_73]),c_0_23])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(k1_tarski(X1),k1_tarski(k1_tarski(esk5_0)))
    | ~ r2_hidden(esk6_0,k5_waybel_0(esk4_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_31]),c_0_27])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_34]),c_0_60]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
