%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t32_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:08 EDT 2019

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   96 (20449 expanded)
%              Number of clauses        :   71 (7558 expanded)
%              Number of leaves         :   12 (4991 expanded)
%              Depth                    :   27
%              Number of atoms          :  332 (109992 expanded)
%              Number of equality atoms :   42 (1757 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',t32_filter_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',t2_subset)).

fof(reflexivity_r3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & v8_lattices(X1)
        & v9_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_lattices(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',reflexivity_r3_lattices)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',fc2_struct_0)).

fof(dt_l1_lattices,axiom,(
    ! [X1] :
      ( l1_lattices(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',dt_l1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',dt_l3_lattices)).

fof(cc1_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1) )
       => ( ~ v2_struct_0(X1)
          & v4_lattices(X1)
          & v5_lattices(X1)
          & v6_lattices(X1)
          & v7_lattices(X1)
          & v8_lattices(X1)
          & v9_lattices(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',cc1_lattices)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',t7_boole)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',fraenkel_a_1_0_filter_1)).

fof(redefinition_k1_domain_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X3,X1)
        & m1_subset_1(X4,X2) )
     => k1_domain_1(X1,X2,X3,X4) = k4_tarski(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',redefinition_k1_domain_1)).

fof(t33_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( k4_tarski(X1,X2) = k4_tarski(X3,X4)
     => ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',t33_zfmisc_1)).

fof(d8_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => k8_filter_1(X1) = a_1_0_filter_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t32_filter_1.p',d8_filter_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X45,X46] :
      ( ~ m1_subset_1(X45,X46)
      | v1_xboole_0(X46)
      | r2_hidden(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & l3_lattices(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & ( ~ r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk3_0),k8_filter_1(esk1_0))
      | ~ r3_lattices(esk1_0,esk2_0,esk3_0) )
    & ( r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk3_0),k8_filter_1(esk1_0))
      | r3_lattices(esk1_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X40,X41,X42] :
      ( v2_struct_0(X40)
      | ~ v6_lattices(X40)
      | ~ v8_lattices(X40)
      | ~ v9_lattices(X40)
      | ~ l3_lattices(X40)
      | ~ m1_subset_1(X41,u1_struct_0(X40))
      | ~ m1_subset_1(X42,u1_struct_0(X40))
      | r3_lattices(X40,X41,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_lattices])])])).

fof(c_0_16,plain,(
    ! [X26] :
      ( v2_struct_0(X26)
      | ~ l1_struct_0(X26)
      | ~ v1_xboole_0(u1_struct_0(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X17] :
      ( ~ l1_lattices(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_lattices])])).

fof(c_0_20,plain,(
    ! [X19] :
      ( ( l1_lattices(X19)
        | ~ l3_lattices(X19) )
      & ( l2_lattices(X19)
        | ~ l3_lattices(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | r3_lattices(X1,X2,X2)
    | ~ v6_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v9_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r3_lattices(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ v9_lattices(X1)
    | ~ v8_lattices(X1)
    | ~ v6_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1) ),
    inference(condense,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_29,plain,(
    ! [X10] :
      ( ( ~ v2_struct_0(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v4_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v5_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v6_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v7_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v8_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) )
      & ( v9_lattices(X10)
        | v2_struct_0(X10)
        | ~ v10_lattices(X10)
        | ~ l3_lattices(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_30,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | ~ v1_xboole_0(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l3_lattices(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X27,X28,X31,X32] :
      ( ( m1_subset_1(esk9_2(X27,X28),u1_struct_0(X28))
        | ~ r2_hidden(X27,a_1_0_filter_1(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( m1_subset_1(esk10_2(X27,X28),u1_struct_0(X28))
        | ~ r2_hidden(X27,a_1_0_filter_1(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( X27 = k1_domain_1(u1_struct_0(X28),u1_struct_0(X28),esk9_2(X27,X28),esk10_2(X27,X28))
        | ~ r2_hidden(X27,a_1_0_filter_1(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( r3_lattices(X28,esk9_2(X27,X28),esk10_2(X27,X28))
        | ~ r2_hidden(X27,a_1_0_filter_1(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ l3_lattices(X28) )
      & ( ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ m1_subset_1(X32,u1_struct_0(X28))
        | X27 != k1_domain_1(u1_struct_0(X28),u1_struct_0(X28),X31,X32)
        | ~ r3_lattices(X28,X31,X32)
        | r2_hidden(X27,a_1_0_filter_1(X28))
        | v2_struct_0(X28)
        | ~ v10_lattices(X28)
        | ~ l3_lattices(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_1_0_filter_1])])])])])])).

cnf(c_0_34,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v9_lattices(esk1_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_28])]),c_0_24])).

cnf(c_0_35,plain,
    ( v9_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_37,plain,(
    ! [X33,X34,X35,X36] :
      ( v1_xboole_0(X33)
      | v1_xboole_0(X34)
      | ~ m1_subset_1(X35,X33)
      | ~ m1_subset_1(X36,X34)
      | k1_domain_1(X33,X34,X35,X36) = k4_tarski(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k1_domain_1])])])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_28])])).

cnf(c_0_40,plain,
    ( r2_hidden(X4,a_1_0_filter_1(X2))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X4 != k1_domain_1(u1_struct_0(X2),u1_struct_0(X2),X1,X3)
    | ~ r3_lattices(X2,X1,X3)
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v8_lattices(esk1_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_42,plain,
    ( v8_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k1_domain_1(X1,X2,X3,X4) = k4_tarski(X3,X4)
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1))
    | v2_struct_0(X1)
    | ~ r3_lattices(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0)
    | ~ v6_lattices(esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_47,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k1_domain_1(X1,u1_struct_0(esk1_0),X2,esk3_0) = k4_tarski(X2,esk3_0)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1,esk3_0),a_1_0_filter_1(esk1_0))
    | ~ r3_lattices(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_18]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( r3_lattices(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_51,negated_conjecture,
    ( k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk3_0,esk3_0) = k4_tarski(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_18]),c_0_44])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk10_2(X1,X2),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,esk3_0),a_1_0_filter_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_18])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk9_2(X1,X2),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( X1 = k1_domain_1(u1_struct_0(X2),u1_struct_0(X2),esk9_2(X1,X2),esk10_2(X1,X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_1_0_filter_1(X2))
    | ~ v10_lattices(X2)
    | ~ l3_lattices(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_57,plain,(
    ! [X50,X51,X52,X53] :
      ( ( X50 = X52
        | k4_tarski(X50,X51) != k4_tarski(X52,X53) )
      & ( X51 = X53
        | k4_tarski(X50,X51) != k4_tarski(X52,X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_zfmisc_1])])])).

cnf(c_0_58,negated_conjecture,
    ( k1_domain_1(X1,u1_struct_0(esk1_0),X2,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) = k4_tarski(X2,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_54]),c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk9_2(k4_tarski(esk3_0,esk3_0),esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_53]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk9_2(k4_tarski(esk3_0,esk3_0),esk1_0),esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) = k4_tarski(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_53]),c_0_28]),c_0_36])]),c_0_24])).

fof(c_0_61,plain,(
    ! [X11] :
      ( v2_struct_0(X11)
      | ~ v10_lattices(X11)
      | ~ l3_lattices(X11)
      | k8_filter_1(X11) = a_1_0_filter_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_filter_1])])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),X1,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)),a_1_0_filter_1(esk1_0))
    | ~ r3_lattices(esk1_0,X1,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_54]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_64,plain,
    ( X1 = X2
    | k4_tarski(X3,X1) != k4_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k4_tarski(esk9_2(k4_tarski(esk3_0,esk3_0),esk1_0),esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) = k4_tarski(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk3_0),k8_filter_1(esk1_0))
    | r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | k8_filter_1(X1) = a_1_0_filter_1(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)),a_1_0_filter_1(esk1_0))
    | ~ r3_lattices(esk1_0,esk2_0,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) = k4_tarski(esk2_0,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_63]),c_0_44])).

cnf(c_0_70,negated_conjecture,
    ( esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0) = X1
    | k4_tarski(esk3_0,esk3_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0)
    | r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk3_0),a_1_0_filter_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_72,negated_conjecture,
    ( k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk3_0) = k4_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_44])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)),a_1_0_filter_1(esk1_0))
    | ~ r3_lattices(esk1_0,esk2_0,esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( esk10_2(k4_tarski(esk3_0,esk3_0),esk1_0) = esk3_0 ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0)
    | r2_hidden(k4_tarski(esk2_0,esk3_0),a_1_0_filter_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),a_1_0_filter_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74]),c_0_74]),c_0_75])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_76]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_78,negated_conjecture,
    ( k1_domain_1(X1,u1_struct_0(esk1_0),X2,esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0)) = k4_tarski(X2,esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_77]),c_0_44])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_76]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0),esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0)) = k4_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_76]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_81,negated_conjecture,
    ( k4_tarski(esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0),esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0)) = k4_tarski(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80]),c_0_44])).

cnf(c_0_82,negated_conjecture,
    ( esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0) = X1
    | k4_tarski(esk2_0,esk3_0) != k4_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0) = esk3_0 ),
    inference(er,[status(thm)],[c_0_82])).

cnf(c_0_84,plain,
    ( r3_lattices(X1,esk9_2(X2,X1),esk10_2(X2,X1))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_1_0_filter_1(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_85,plain,
    ( X1 = X2
    | k4_tarski(X1,X3) != k4_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_86,negated_conjecture,
    ( k4_tarski(esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0),esk3_0) = k4_tarski(esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r3_lattices(esk1_0,esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0),esk10_2(k4_tarski(esk2_0,esk3_0),esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_76]),c_0_28]),c_0_36])]),c_0_24])).

cnf(c_0_88,negated_conjecture,
    ( esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0) = X1
    | k4_tarski(esk2_0,esk3_0) != k4_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(esk1_0),u1_struct_0(esk1_0),esk2_0,esk3_0),k8_filter_1(esk1_0))
    | ~ r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_90,negated_conjecture,
    ( r3_lattices(esk1_0,esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0),esk3_0) ),
    inference(rw,[status(thm)],[c_0_87,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( esk9_2(k4_tarski(esk2_0,esk3_0),esk1_0) = esk2_0 ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( ~ r3_lattices(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k8_filter_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_89,c_0_72])).

cnf(c_0_93,negated_conjecture,
    ( r3_lattices(esk1_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(esk2_0,esk3_0),k8_filter_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_67]),c_0_76]),c_0_28]),c_0_36])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
