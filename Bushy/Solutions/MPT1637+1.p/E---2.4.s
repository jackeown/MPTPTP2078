%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t17_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:45 EDT 2019

% Result     : Theorem 0.81s
% Output     : CNFRefutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   86 (2362 expanded)
%              Number of clauses        :   61 ( 886 expanded)
%              Number of leaves         :   12 ( 560 expanded)
%              Depth                    :   20
%              Number of atoms          :  289 (10892 expanded)
%              Number of equality atoms :   40 ( 396 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',t17_waybel_0)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',dt_k6_domain_1)).

fof(d17_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k5_waybel_0(X1,X2) = k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',d17_waybel_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',t5_subset)).

fof(dt_k5_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',dt_k5_waybel_0)).

fof(t14_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k3_waybel_0(X1,X2) = a_2_0_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',t14_waybel_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',redefinition_k6_domain_1)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',fraenkel_a_2_0_waybel_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',d1_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',t4_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t17_waybel_0.p',dt_l1_orders_2)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | m1_subset_1(k6_domain_1(X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r2_hidden(esk3_0,k5_waybel_0(esk1_0,esk2_0))
      | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) )
    & ( r2_hidden(esk3_0,k5_waybel_0(esk1_0,esk2_0))
      | r1_orders_2(esk1_0,esk3_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( v2_struct_0(X11)
      | ~ l1_orders_2(X11)
      | ~ m1_subset_1(X12,u1_struct_0(X11))
      | k5_waybel_0(X11,X12) = k3_waybel_0(X11,k6_domain_1(u1_struct_0(X11),X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_waybel_0])])])])).

fof(c_0_16,plain,(
    ! [X62,X63,X64] :
      ( ~ r2_hidden(X62,X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(X64))
      | ~ v1_xboole_0(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | m1_subset_1(k5_waybel_0(X22,X23),k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k5_waybel_0])])])).

fof(c_0_18,plain,(
    ! [X48,X49] :
      ( v2_struct_0(X48)
      | ~ l1_orders_2(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | k3_waybel_0(X48,X49) = a_2_0_waybel_0(X48,X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_waybel_0])])])])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | k5_waybel_0(X1,X2) = k3_waybel_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,k5_waybel_0(esk1_0,esk2_0))
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k5_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | k3_waybel_0(X1,X2) = a_2_0_waybel_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k3_waybel_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0)) = k5_waybel_0(esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_22])]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k5_waybel_0(esk1_0,esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k5_waybel_0(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_20]),c_0_22])]),c_0_23])).

fof(c_0_32,plain,(
    ! [X46,X47] :
      ( v1_xboole_0(X46)
      | ~ m1_subset_1(X47,X46)
      | k6_domain_1(X46,X47) = k1_tarski(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_33,negated_conjecture,
    ( k5_waybel_0(esk1_0,esk2_0) = a_2_0_waybel_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X32,X33,X34,X37,X38] :
      ( ( m1_subset_1(esk8_3(X32,X33,X34),u1_struct_0(X33))
        | ~ r2_hidden(X32,a_2_0_waybel_0(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( X32 = esk8_3(X32,X33,X34)
        | ~ r2_hidden(X32,a_2_0_waybel_0(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( m1_subset_1(esk9_3(X32,X33,X34),u1_struct_0(X33))
        | ~ r2_hidden(X32,a_2_0_waybel_0(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( r1_orders_2(X33,esk8_3(X32,X33,X34),esk9_3(X32,X33,X34))
        | ~ r2_hidden(X32,a_2_0_waybel_0(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( r2_hidden(esk9_3(X32,X33,X34),X34)
        | ~ r2_hidden(X32,a_2_0_waybel_0(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) )
      & ( ~ m1_subset_1(X37,u1_struct_0(X33))
        | X32 != X37
        | ~ m1_subset_1(X38,u1_struct_0(X33))
        | ~ r1_orders_2(X33,X37,X38)
        | ~ r2_hidden(X38,X34)
        | r2_hidden(X32,a_2_0_waybel_0(X33,X34))
        | v2_struct_0(X33)
        | ~ l1_orders_2(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_waybel_0])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_hidden(esk3_0,a_2_0_waybel_0(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk9_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_hidden(esk3_0,a_2_0_waybel_0(esk1_0,k1_tarski(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_34])).

fof(c_0_41,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X13
        | X14 != k1_tarski(X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k1_tarski(X13) )
      & ( ~ r2_hidden(esk4_2(X17,X18),X18)
        | esk4_2(X17,X18) != X17
        | X18 = k1_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X18)
        | esk4_2(X17,X18) = X17
        | X18 = k1_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | m1_subset_1(esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22])]),c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_38])).

cnf(c_0_45,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_hidden(esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | ~ m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_22])]),c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | m1_subset_1(esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_34])).

cnf(c_0_48,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_hidden(esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_44]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0))),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_47]),c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0))) = k1_tarski(esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)))
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_47]),c_0_34])).

cnf(c_0_53,plain,
    ( r1_orders_2(X1,esk8_3(X2,X1,X3),esk9_3(X2,X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_0_waybel_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | m1_subset_1(k6_domain_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk3_0,esk1_0,k1_tarski(esk2_0)),esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)))
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_40]),c_0_22])]),c_0_23])).

cnf(c_0_57,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0)
    | m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,plain,
    ( X1 = esk8_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_59,plain,(
    ! [X59,X60,X61] :
      ( ~ r2_hidden(X59,X60)
      | ~ m1_subset_1(X60,k1_zfmisc_1(X61))
      | m1_subset_1(X59,X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_60,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk3_0,esk1_0,k1_tarski(esk2_0)),esk9_3(esk3_0,esk1_0,k1_tarski(esk2_0)))
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( esk8_3(esk3_0,esk1_0,k1_tarski(esk2_0)) = esk3_0
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_40]),c_0_22])]),c_0_23])).

cnf(c_0_62,plain,
    ( r2_hidden(X3,a_2_0_waybel_0(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r2_hidden(X4,X5)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r1_orders_2(esk1_0,esk8_3(esk3_0,esk1_0,k1_tarski(esk2_0)),esk2_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( esk8_3(esk3_0,esk1_0,k1_tarski(esk2_0)) = esk3_0
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_44]),c_0_34])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,a_2_0_waybel_0(X2,X3))
    | v2_struct_0(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_67,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_70,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k5_waybel_0(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_71,negated_conjecture,
    ( k3_waybel_0(esk1_0,k1_tarski(esk2_0)) = k5_waybel_0(esk1_0,esk2_0)
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_72,negated_conjecture,
    ( k3_waybel_0(esk1_0,k1_tarski(esk2_0)) = a_2_0_waybel_0(esk1_0,k1_tarski(esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_44]),c_0_22])]),c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_0_waybel_0(esk1_0,X1))
    | ~ r2_hidden(esk2_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_22])]),c_0_23])).

cnf(c_0_74,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_69])])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k5_waybel_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_67])])).

cnf(c_0_76,negated_conjecture,
    ( k5_waybel_0(esk1_0,esk2_0) = a_2_0_waybel_0(esk1_0,k1_tarski(esk2_0))
    | v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

fof(c_0_77,plain,(
    ! [X31] :
      ( v2_struct_0(X31)
      | ~ l1_struct_0(X31)
      | ~ v1_xboole_0(u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk3_0,a_2_0_waybel_0(esk1_0,k1_tarski(esk2_0)))
    | ~ m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r2_hidden(esk3_0,a_2_0_waybel_0(esk1_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_44]),c_0_79])).

fof(c_0_82,plain,(
    ! [X26] :
      ( ~ l1_orders_2(X26)
      | l1_struct_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_23])).

cnf(c_0_84,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_22])]),
    [proof]).
%------------------------------------------------------------------------------
