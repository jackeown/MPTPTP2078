%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1638+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:30 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   65 (1017 expanded)
%              Number of clauses        :   46 ( 380 expanded)
%              Number of leaves         :    9 ( 248 expanded)
%              Depth                    :   20
%              Number of atoms          :  243 (4466 expanded)
%              Number of equality atoms :   39 ( 259 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k6_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_waybel_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

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

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t15_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k4_waybel_0(X1,X2) = a_2_1_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_waybel_0)).

fof(d18_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k6_waybel_0(X1,X2) = k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_0)).

fof(fraenkel_a_2_1_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_waybel_0(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r1_orders_2(X2,X5,X4)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k6_waybel_0(X1,X2))
                <=> r1_orders_2(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_waybel_0])).

fof(c_0_10,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
    & ( ~ r2_hidden(esk8_0,k6_waybel_0(esk6_0,esk7_0))
      | ~ r1_orders_2(esk6_0,esk7_0,esk8_0) )
    & ( r2_hidden(esk8_0,k6_waybel_0(esk6_0,esk7_0))
      | r1_orders_2(esk6_0,esk7_0,esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k1_tarski(esk7_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_18,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_19,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_20,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k1_tarski(esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | k4_waybel_0(X35,X36) = a_2_1_waybel_0(X35,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t15_waybel_0])])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k1_tarski(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

fof(c_0_26,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | k6_waybel_0(X6,X7) = k4_waybel_0(X6,k6_domain_1(u1_struct_0(X6),X7)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d18_waybel_0])])])])).

fof(c_0_27,plain,(
    ! [X19,X20,X21,X24,X25] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( X19 = esk2_3(X19,X20,X21)
        | ~ r2_hidden(X19,a_2_1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( m1_subset_1(esk3_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r1_orders_2(X20,esk3_3(X19,X20,X21),esk2_3(X19,X20,X21))
        | ~ r2_hidden(X19,a_2_1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r2_hidden(esk3_3(X19,X20,X21),X21)
        | ~ r2_hidden(X19,a_2_1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | ~ m1_subset_1(X25,u1_struct_0(X20))
        | ~ r1_orders_2(X20,X25,X24)
        | ~ r2_hidden(X25,X21)
        | r2_hidden(X19,a_2_1_waybel_0(X20,X21))
        | v2_struct_0(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_waybel_0])])])])])])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | k4_waybel_0(X1,X2) = a_2_1_waybel_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | m1_subset_1(k1_tarski(esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_14])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | k6_waybel_0(X1,X2) = k4_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k4_waybel_0(esk6_0,k1_tarski(esk7_0)) = a_2_1_waybel_0(esk6_0,k1_tarski(esk7_0))
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_22])]),c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k4_waybel_0(esk6_0,k1_tarski(esk7_0)) = k6_waybel_0(esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_14]),c_0_25]),c_0_22])]),c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( esk2_3(X1,esk6_0,k1_tarski(esk7_0)) = X1
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,a_2_1_waybel_0(esk6_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_22])]),c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( a_2_1_waybel_0(esk6_0,k1_tarski(esk7_0)) = k6_waybel_0(esk6_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( esk2_3(X1,esk6_0,k1_tarski(esk7_0)) = X1
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k6_waybel_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk8_0,k6_waybel_0(esk6_0,esk7_0))
    | r1_orders_2(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_39,plain,(
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

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk3_3(X1,esk6_0,k1_tarski(esk7_0)),k1_tarski(esk7_0))
    | ~ r2_hidden(X1,a_2_1_waybel_0(esk6_0,k1_tarski(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_29]),c_0_22])]),c_0_17])).

cnf(c_0_41,plain,
    ( r1_orders_2(X1,esk3_3(X2,X1,X3),esk2_3(X2,X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_waybel_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( esk2_3(esk8_0,esk6_0,k1_tarski(esk7_0)) = esk8_0
    | r1_orders_2(esk6_0,esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk3_3(X1,esk6_0,k1_tarski(esk7_0)),k1_tarski(esk7_0))
    | ~ r2_hidden(X1,k6_waybel_0(esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk6_0,esk3_3(esk8_0,esk6_0,k1_tarski(esk7_0)),esk8_0)
    | r1_orders_2(esk6_0,esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ r2_hidden(esk8_0,a_2_1_waybel_0(esk6_0,k1_tarski(esk7_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_22])]),c_0_17]),c_0_29])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk6_0,esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk3_3(esk8_0,esk6_0,k1_tarski(esk7_0)),k1_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( r1_orders_2(esk6_0,esk3_3(esk8_0,esk6_0,k1_tarski(esk7_0)),esk8_0)
    | r1_orders_2(esk6_0,esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_35]),c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( esk3_3(esk8_0,esk6_0,k1_tarski(esk7_0)) = esk7_0
    | r1_orders_2(esk6_0,esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,a_2_1_waybel_0(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X5)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk6_0,esk7_0,esk8_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,a_2_1_waybel_0(X2,X3))
    | v2_struct_0(X2)
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk6_0,esk7_0,esk8_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_51]),c_0_17])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(X1,k6_waybel_0(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,X2,X1)
    | ~ r2_hidden(X2,k1_tarski(esk7_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_35]),c_0_22])]),c_0_17]),c_0_29])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k6_waybel_0(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk6_0,esk7_0,esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_21]),c_0_22])])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(X1,k6_waybel_0(esk6_0,esk7_0))
    | ~ r1_orders_2(esk6_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_14])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k6_waybel_0(esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_60])]),c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_62]),c_0_17])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_21]),c_0_22])]),
    [proof]).

%------------------------------------------------------------------------------
