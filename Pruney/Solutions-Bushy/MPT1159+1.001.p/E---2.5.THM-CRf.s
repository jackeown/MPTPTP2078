%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1159+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 307 expanded)
%              Number of clauses        :   34 ( 104 expanded)
%              Number of leaves         :    5 (  73 expanded)
%              Depth                    :    9
%              Number of atoms          :  188 (2586 expanded)
%              Number of equality atoms :   19 (  76 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_orders_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v3_orders_2(X5)
      | ~ v4_orders_2(X5)
      | ~ v5_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | k3_orders_2(X5,X6,X7) = k9_subset_1(u1_struct_0(X5),k2_orders_2(X5,k6_domain_1(u1_struct_0(X5),X7)),X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_orders_2])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ r2_hidden(esk3_0,k3_orders_2(esk2_0,esk5_0,esk4_0))
      | ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
      | ~ r2_hidden(esk3_0,esk5_0) )
    & ( r2_orders_2(esk2_0,esk3_0,esk4_0)
      | r2_hidden(esk3_0,k3_orders_2(esk2_0,esk5_0,esk4_0)) )
    & ( r2_hidden(esk3_0,esk5_0)
      | r2_hidden(esk3_0,k3_orders_2(esk2_0,esk5_0,esk4_0)) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X17,X18,X19] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(X17))
      | k9_subset_1(X17,X18,X19) = k3_xboole_0(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] :
      ( ( ~ r2_orders_2(X20,X21,X22)
        | r2_hidden(X21,k2_orders_2(X20,k6_domain_1(u1_struct_0(X20),X22)))
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20) )
      & ( ~ r2_hidden(X21,k2_orders_2(X20,k6_domain_1(u1_struct_0(X20),X22)))
        | r2_orders_2(X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | ~ m1_subset_1(X21,u1_struct_0(X20))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_orders_2])])])])])).

fof(c_0_19,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( r2_hidden(X11,X8)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(X12,X8)
        | ~ r2_hidden(X12,X9)
        | r2_hidden(X12,X10)
        | X10 != k3_xboole_0(X8,X9) )
      & ( ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X13)
        | ~ r2_hidden(esk1_3(X13,X14,X15),X14)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X13)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X14)
        | r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k3_xboole_0(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_20,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),X1) = k3_orders_2(esk2_0,X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk2_0),X1,esk5_0) = k3_xboole_0(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( r2_orders_2(X2,X1,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k2_orders_2(X2,k6_domain_1(u1_struct_0(X2),X3)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0)
    | r2_hidden(esk3_0,k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( k3_orders_2(esk2_0,esk5_0,esk4_0) = k3_xboole_0(k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_17]),c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( r2_orders_2(esk2_0,X1,esk4_0)
    | ~ r2_hidden(X1,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0)
    | r2_hidden(esk3_0,k3_orders_2(esk2_0,esk5_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0)
    | r2_hidden(esk3_0,k3_xboole_0(k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),esk5_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_orders_2(esk2_0,esk5_0,esk4_0))
    | ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk3_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_26]),c_0_31])).

cnf(c_0_38,plain,
    ( r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( r2_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_orders_2(esk2_0,esk3_0,esk4_0)
    | ~ r2_hidden(esk3_0,k3_xboole_0(k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),esk5_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_26]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk3_0,k3_xboole_0(X1,esk5_0))
    | ~ r2_hidden(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_10]),c_0_28]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k3_xboole_0(k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk4_0)),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_39])])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),
    [proof]).

%------------------------------------------------------------------------------
