%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1437+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 401 expanded)
%              Number of clauses        :   38 ( 141 expanded)
%              Number of leaves         :    8 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 (2553 expanded)
%              Number of equality atoms :   32 ( 143 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fraenkel_a_1_0_filter_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X2)
        & v10_lattices(X2)
        & l3_lattices(X2) )
     => ( r2_hidden(X1,a_1_0_filter_1(X2))
      <=> ? [X3,X4] :
            ( m1_subset_1(X3,u1_struct_0(X2))
            & m1_subset_1(X4,u1_struct_0(X2))
            & X1 = k1_domain_1(u1_struct_0(X2),u1_struct_0(X2),X3,X4)
            & r3_lattices(X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_1_0_filter_1)).

fof(redefinition_k1_domain_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X2) )
     => k1_domain_1(X1,X2,X3,X4) = k4_tarski(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(t32_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))
              <=> r3_lattices(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_filter_1)).

fof(d8_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => k8_filter_1(X1) = a_1_0_filter_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_filter_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_zfmisc_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l2_lattices,axiom,(
    ! [X1] :
      ( l2_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(c_0_8,plain,(
    ! [X10,X11,X14,X15] :
      ( ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X11))
        | ~ r2_hidden(X10,a_1_0_filter_1(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( m1_subset_1(esk2_2(X10,X11),u1_struct_0(X11))
        | ~ r2_hidden(X10,a_1_0_filter_1(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( X10 = k1_domain_1(u1_struct_0(X11),u1_struct_0(X11),esk1_2(X10,X11),esk2_2(X10,X11))
        | ~ r2_hidden(X10,a_1_0_filter_1(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( r3_lattices(X11,esk1_2(X10,X11),esk2_2(X10,X11))
        | ~ r2_hidden(X10,a_1_0_filter_1(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ m1_subset_1(X15,u1_struct_0(X11))
        | X10 != k1_domain_1(u1_struct_0(X11),u1_struct_0(X11),X14,X15)
        | ~ r3_lattices(X11,X14,X15)
        | r2_hidden(X10,a_1_0_filter_1(X11))
        | v2_struct_0(X11)
        | ~ v10_lattices(X11)
        | ~ l3_lattices(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_1_0_filter_1])])])])])])).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19] :
      ( v1_xboole_0(X16)
      | v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X16)
      | ~ m1_subset_1(X19,X17)
      | k1_domain_1(X16,X17,X18,X19) = k4_tarski(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k1_domain_1])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))
                <=> r3_lattices(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_filter_1])).

cnf(c_0_11,plain,
    ( r2_hidden(X4,a_1_0_filter_1(X2))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X4 != k1_domain_1(u1_struct_0(X2),u1_struct_0(X2),X1,X3)
    | ~ r3_lattices(X2,X1,X3)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X6] :
      ( v2_struct_0(X6)
      | ~ v10_lattices(X6)
      | ~ l3_lattices(X6)
      | k8_filter_1(X6) = a_1_0_filter_1(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_filter_1])])])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X25 = X27
        | k4_tarski(X25,X26) != k4_tarski(X27,X28) )
      & ( X26 = X28
        | k4_tarski(X25,X26) != k4_tarski(X27,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k1_domain_1(X1,X2,X3,X4) = k4_tarski(X3,X4)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k1_domain_1(u1_struct_0(X2),u1_struct_0(X2),esk1_2(X1,X2),esk2_2(X1,X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( m1_subset_1(esk2_2(X1,X2),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v10_lattices(esk3_0)
    & l3_lattices(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ( ~ r2_hidden(k1_domain_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0,esk5_0),k8_filter_1(esk3_0))
      | ~ r3_lattices(esk3_0,esk4_0,esk5_0) )
    & ( r2_hidden(k1_domain_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0,esk5_0),k8_filter_1(esk3_0))
      | r3_lattices(esk3_0,esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | k8_filter_1(X1) = a_1_0_filter_1(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2)) = X1
    | v1_xboole_0(u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k1_domain_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0,esk5_0),k8_filter_1(esk3_0))
    | r3_lattices(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(esk3_0),u1_struct_0(esk3_0),esk4_0,esk5_0),k8_filter_1(esk3_0))
    | ~ r3_lattices(esk3_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),k8_filter_1(X1))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v10_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( l3_lattices(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( esk2_2(k4_tarski(X1,X2),X3) = X2
    | v1_xboole_0(u1_struct_0(X3))
    | v2_struct_0(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),a_1_0_filter_1(X3))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( r3_lattices(esk3_0,esk4_0,esk5_0)
    | r2_hidden(k4_tarski(esk4_0,esk5_0),k8_filter_1(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_14]),c_0_24]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r3_lattices(esk3_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24]),c_0_25]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_34,plain,
    ( esk2_2(k4_tarski(X1,X2),X3) = X2
    | v1_xboole_0(u1_struct_0(X3))
    | v2_struct_0(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k8_filter_1(X3))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_0,esk5_0),k8_filter_1(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( esk2_2(k4_tarski(esk4_0,esk5_0),esk3_0) = esk5_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_37,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( k4_tarski(esk1_2(k4_tarski(esk4_0,esk5_0),esk3_0),esk5_0) = k4_tarski(esk4_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(k4_tarski(esk4_0,esk5_0),a_1_0_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_36]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk1_2(k4_tarski(esk4_0,esk5_0),esk3_0) = X1
    | v1_xboole_0(u1_struct_0(esk3_0))
    | k4_tarski(esk4_0,esk5_0) != k4_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_0,esk5_0),a_1_0_filter_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_40,plain,
    ( r3_lattices(X1,esk1_2(X2,X1),esk2_2(X2,X1))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_1_0_filter_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_41,negated_conjecture,
    ( esk1_2(k4_tarski(esk4_0,esk5_0),esk3_0) = X1
    | v1_xboole_0(u1_struct_0(esk3_0))
    | k4_tarski(esk4_0,esk5_0) != k4_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_28]),c_0_29])]),c_0_30]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r3_lattices(esk3_0,esk1_2(k4_tarski(esk4_0,esk5_0),esk3_0),esk5_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(k4_tarski(esk4_0,esk5_0),a_1_0_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( esk1_2(k4_tarski(esk4_0,esk5_0),esk3_0) = esk4_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_44,plain,(
    ! [X9] :
      ( v2_struct_0(X9)
      | ~ l1_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(k4_tarski(esk4_0,esk5_0),a_1_0_filter_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_33])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_28]),c_0_29])]),c_0_30]),c_0_35])).

fof(c_0_48,plain,(
    ! [X7] :
      ( ~ l2_lattices(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l2_lattices])])).

cnf(c_0_49,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l2_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_51,plain,(
    ! [X8] :
      ( ( l1_lattices(X8)
        | ~ l3_lattices(X8) )
      & ( l2_lattices(X8)
        | ~ l3_lattices(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_52,negated_conjecture,
    ( ~ l2_lattices(esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_53,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
