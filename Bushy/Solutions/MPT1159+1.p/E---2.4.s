%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t57_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:22 EDT 2019

% Result     : Theorem 1.09s
% Output     : CNFRefutation 1.09s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 364 expanded)
%              Number of clauses        :   33 ( 123 expanded)
%              Number of leaves         :    6 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  239 (3118 expanded)
%              Number of equality atoms :   19 ( 109 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',d4_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',redefinition_k9_subset_1)).

fof(d14_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',d14_orders_2)).

fof(t57_orders_2,conjecture,(
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
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                  <=> ( r2_orders_2(X1,X2,X3)
                      & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t57_orders_2)).

fof(t52_orders_2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t52_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t4_subset)).

fof(c_0_6,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X26)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_7,plain,(
    ! [X60,X61,X62] :
      ( ~ m1_subset_1(X62,k1_zfmisc_1(X60))
      | k9_subset_1(X60,X61,X62) = k3_xboole_0(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ v4_orders_2(X17)
      | ~ v5_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | k3_orders_2(X17,X18,X19) = k9_subset_1(u1_struct_0(X17),k2_orders_2(X17,k6_domain_1(u1_struct_0(X17),X19)),X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_orders_2])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

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
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( r2_hidden(X2,k3_orders_2(X1,X4,X3))
                    <=> ( r2_orders_2(X1,X2,X3)
                        & r2_hidden(X2,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t57_orders_2])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_xboole_0(k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X3) = k3_orders_2(X1,X3,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0))
      | ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
      | ~ r2_hidden(esk2_0,esk4_0) )
    & ( r2_orders_2(esk1_0,esk2_0,esk3_0)
      | r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0)) )
    & ( r2_hidden(esk2_0,esk4_0)
      | r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_17,plain,(
    ! [X76,X77,X78] :
      ( ( ~ r2_orders_2(X76,X77,X78)
        | r2_hidden(X77,k2_orders_2(X76,k6_domain_1(u1_struct_0(X76),X78)))
        | ~ m1_subset_1(X78,u1_struct_0(X76))
        | ~ m1_subset_1(X77,u1_struct_0(X76))
        | v2_struct_0(X76)
        | ~ v3_orders_2(X76)
        | ~ v4_orders_2(X76)
        | ~ v5_orders_2(X76)
        | ~ l1_orders_2(X76) )
      & ( ~ r2_hidden(X77,k2_orders_2(X76,k6_domain_1(u1_struct_0(X76),X78)))
        | r2_orders_2(X76,X77,X78)
        | ~ m1_subset_1(X78,u1_struct_0(X76))
        | ~ m1_subset_1(X77,u1_struct_0(X76))
        | v2_struct_0(X76)
        | ~ v3_orders_2(X76)
        | ~ v4_orders_2(X76)
        | ~ v5_orders_2(X76)
        | ~ l1_orders_2(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_orders_2])])])])])).

fof(c_0_18,plain,(
    ! [X73,X74,X75] :
      ( ~ r2_hidden(X73,X74)
      | ~ m1_subset_1(X74,k1_zfmisc_1(X75))
      | m1_subset_1(X73,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,k3_orders_2(X3,X2,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v3_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0)
    | r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | X2 != k3_orders_2(X3,X4,X5)
    | ~ r2_hidden(X1,k2_orders_2(X3,k6_domain_1(u1_struct_0(X3),X5)))
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v3_orders_2(X3) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14])).

cnf(c_0_29,plain,
    ( r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0))
    | ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | X2 != k3_orders_2(X3,X4,X5)
    | ~ r2_orders_2(X3,X1,X5)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | ~ v5_orders_2(X3)
    | ~ v4_orders_2(X3)
    | ~ v3_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_orders_2(X2,X3,X4))
    | v2_struct_0(X2)
    | ~ r2_orders_2(X2,X1,X4)
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_32]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_orders_2(X2,k6_domain_1(u1_struct_0(X2),X3)))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k3_orders_2(X2,X4,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_0,k3_orders_2(esk1_0,esk4_0,esk3_0)) ),
    inference(sr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,plain,
    ( r2_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k2_orders_2(X2,k6_domain_1(u1_struct_0(X2),X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_0,k2_orders_2(esk1_0,k6_domain_1(u1_struct_0(esk1_0),esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_22]),c_0_44]),c_0_23]),c_0_24]),c_0_25]),c_0_26])]),c_0_39]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
