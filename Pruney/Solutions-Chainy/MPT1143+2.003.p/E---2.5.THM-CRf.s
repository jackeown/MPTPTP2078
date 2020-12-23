%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:32 EST 2020

% Result     : Theorem 0.43s
% Output     : CNFRefutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 295 expanded)
%              Number of clauses        :   54 ( 130 expanded)
%              Number of leaves         :   14 (  71 expanded)
%              Depth                    :   19
%              Number of atoms          :  274 (1104 expanded)
%              Number of equality atoms :   52 ( 249 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   3 average)
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

fof(t35_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
            & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(d7_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r7_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_14,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( ~ r2_hidden(X7,X6)
        | X7 = X5
        | X6 != k1_tarski(X5) )
      & ( X8 != X5
        | r2_hidden(X8,X6)
        | X6 != k1_tarski(X5) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) != X9
        | X10 = k1_tarski(X9) )
      & ( r2_hidden(esk1_2(X9,X10),X10)
        | esk1_2(X9,X10) = X9
        | X10 = k1_tarski(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_15,plain,(
    ! [X12] : k2_tarski(X12,X12) = k1_tarski(X12) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_16,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_18,plain,(
    ! [X34,X35] :
      ( v1_xboole_0(X34)
      | ~ m1_subset_1(X35,X34)
      | k6_domain_1(X34,X35) = k1_tarski(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_19,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_22,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
              & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_orders_2])).

cnf(c_0_25,plain,
    ( X1 = X2
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X2,X3)
    | ~ r2_hidden(X1,k6_domain_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) = X1
    | r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_17])).

fof(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).

cnf(c_0_28,plain,
    ( esk1_2(X1,k6_domain_1(X2,X3)) = X1
    | k6_domain_1(X2,X3) = k2_tarski(X1,X1)
    | esk1_2(X1,k6_domain_1(X2,X3)) = X3
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X3,X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(X1,X1)
    | esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = X1
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_30,c_0_17])).

cnf(c_0_33,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(X1,X1)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | X1 != esk5_0 ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_32])).

fof(c_0_36,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | m1_subset_1(k6_domain_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_37,plain,(
    ! [X18,X19] :
      ( ( ~ v6_orders_2(X19,X18)
        | r7_relat_2(u1_orders_2(X18),X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( ~ r7_relat_2(u1_orders_2(X18),X19)
        | v6_orders_2(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_38,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk1_2(X1,X2) != X1
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_33,c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | esk1_2(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_43,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( ~ r7_relat_2(X20,X21)
        | ~ r2_hidden(X22,X21)
        | ~ r2_hidden(X23,X21)
        | r2_hidden(k4_tarski(X22,X23),X20)
        | r2_hidden(k4_tarski(X23,X22),X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk2_2(X20,X24),X24)
        | r7_relat_2(X20,X24)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_2(X20,X24),X24)
        | r7_relat_2(X20,X24)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X20,X24),esk3_2(X20,X24)),X20)
        | r7_relat_2(X20,X24)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X20,X24),esk2_2(X20,X24)),X20)
        | r7_relat_2(X20,X24)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_44,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X2,k6_domain_1(X1,X2))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ r7_relat_2(u1_orders_2(X1),k6_domain_1(u1_struct_0(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_29])])).

cnf(c_0_51,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_22]),c_0_29])])).

cnf(c_0_53,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( esk2_2(X1,k2_tarski(X2,X2)) = X2
    | r7_relat_2(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_29])]),c_0_52])).

cnf(c_0_57,plain,
    ( esk3_2(X1,k2_tarski(X2,X2)) = X2
    | r7_relat_2(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_53])).

cnf(c_0_58,plain,
    ( r7_relat_2(X1,k2_tarski(X2,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(k4_tarski(X2,esk3_2(X1,k2_tarski(X2,X2))),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_relat_1(u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

fof(c_0_60,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_orders_2(X27,X28,X29)
        | r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))
        | r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_relat_1(u1_orders_2(esk4_0))
    | ~ r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

fof(c_0_63,plain,(
    ! [X36,X37] :
      ( v2_struct_0(X36)
      | ~ v3_orders_2(X36)
      | ~ l1_orders_2(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | r1_orders_2(X36,X37,X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_64,plain,(
    ! [X17] :
      ( v2_struct_0(X17)
      | ~ l1_struct_0(X17)
      | ~ v1_xboole_0(u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ v1_relat_1(u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_51]),c_0_29])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_69,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_70,plain,(
    ! [X33] :
      ( ~ l1_orders_2(X33)
      | m1_subset_1(u1_orders_2(X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_71,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_relat_1(u1_orders_2(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67]),c_0_51]),c_0_29])]),c_0_68])).

cnf(c_0_74,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_76,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ v1_relat_1(u1_orders_2(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_68])).

cnf(c_0_78,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

fof(c_0_79,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | l1_struct_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_80,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_51])])).

cnf(c_0_81,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_51])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.43/0.60  # AutoSched0-Mode selected heuristic G_E___092_C01_F1_PI_AE_Q4_CS_SP_PS_S0Y
% 0.43/0.60  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.43/0.60  #
% 0.43/0.60  # Preprocessing time       : 0.028 s
% 0.43/0.60  # Presaturation interreduction done
% 0.43/0.60  
% 0.43/0.60  # Proof found!
% 0.43/0.60  # SZS status Theorem
% 0.43/0.60  # SZS output start CNFRefutation
% 0.43/0.60  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.43/0.60  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.43/0.60  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.43/0.60  fof(t35_orders_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 0.43/0.60  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.43/0.60  fof(d11_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_orders_2(X2,X1)<=>r7_relat_2(u1_orders_2(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 0.43/0.60  fof(d7_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r7_relat_2(X1,X2)<=>![X3, X4]:~((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&~(r2_hidden(k4_tarski(X3,X4),X1)))&~(r2_hidden(k4_tarski(X4,X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_2)).
% 0.43/0.60  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.43/0.60  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.43/0.60  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.43/0.60  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.43/0.60  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.43/0.60  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.43/0.60  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.43/0.60  fof(c_0_14, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.43/0.60  fof(c_0_15, plain, ![X12]:k2_tarski(X12,X12)=k1_tarski(X12), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.43/0.60  cnf(c_0_16, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.43/0.60  fof(c_0_18, plain, ![X34, X35]:(v1_xboole_0(X34)|~m1_subset_1(X35,X34)|k6_domain_1(X34,X35)=k1_tarski(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.43/0.60  cnf(c_0_19, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.43/0.60  cnf(c_0_20, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.43/0.60  cnf(c_0_21, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_19])).
% 0.43/0.60  cnf(c_0_22, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.43/0.60  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  fof(c_0_24, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t35_orders_2])).
% 0.43/0.60  cnf(c_0_25, plain, (X1=X2|v1_xboole_0(X3)|~m1_subset_1(X2,X3)|~r2_hidden(X1,k6_domain_1(X3,X2))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.43/0.60  cnf(c_0_26, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)=X1|r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_23, c_0_17])).
% 0.43/0.60  fof(c_0_27, negated_conjecture, (((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(~v6_orders_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])).
% 0.43/0.60  cnf(c_0_28, plain, (esk1_2(X1,k6_domain_1(X2,X3))=X1|k6_domain_1(X2,X3)=k2_tarski(X1,X1)|esk1_2(X1,k6_domain_1(X2,X3))=X3|v1_xboole_0(X2)|~m1_subset_1(X3,X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.43/0.60  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.60  cnf(c_0_30, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_31, negated_conjecture, (esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(X1,X1)|esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=X1|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.43/0.60  cnf(c_0_32, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_30, c_0_17])).
% 0.43/0.60  cnf(c_0_33, plain, (X2=k1_tarski(X1)|~r2_hidden(esk1_2(X1,X2),X2)|esk1_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.43/0.60  cnf(c_0_34, negated_conjecture, (esk1_2(X1,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(X1,X1)|v1_xboole_0(u1_struct_0(esk4_0))|X1!=esk5_0), inference(ef,[status(thm)],[c_0_31])).
% 0.43/0.60  cnf(c_0_35, plain, (r2_hidden(X1,X2)|X2!=k2_tarski(X1,X1)), inference(er,[status(thm)],[c_0_32])).
% 0.43/0.60  fof(c_0_36, plain, ![X30, X31]:(v1_xboole_0(X30)|~m1_subset_1(X31,X30)|m1_subset_1(k6_domain_1(X30,X31),k1_zfmisc_1(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.43/0.60  fof(c_0_37, plain, ![X18, X19]:((~v6_orders_2(X19,X18)|r7_relat_2(u1_orders_2(X18),X19)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18))&(~r7_relat_2(u1_orders_2(X18),X19)|v6_orders_2(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|~l1_orders_2(X18))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).
% 0.43/0.60  cnf(c_0_38, plain, (X2=k2_tarski(X1,X1)|esk1_2(X1,X2)!=X1|~r2_hidden(esk1_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_33, c_0_17])).
% 0.43/0.60  cnf(c_0_39, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|esk1_2(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(er,[status(thm)],[c_0_34])).
% 0.43/0.60  cnf(c_0_40, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[c_0_35])).
% 0.43/0.60  cnf(c_0_41, negated_conjecture, (~v6_orders_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.60  cnf(c_0_42, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.43/0.60  fof(c_0_43, plain, ![X20, X21, X22, X23, X24]:((~r7_relat_2(X20,X21)|(~r2_hidden(X22,X21)|~r2_hidden(X23,X21)|r2_hidden(k4_tarski(X22,X23),X20)|r2_hidden(k4_tarski(X23,X22),X20))|~v1_relat_1(X20))&((((r2_hidden(esk2_2(X20,X24),X24)|r7_relat_2(X20,X24)|~v1_relat_1(X20))&(r2_hidden(esk3_2(X20,X24),X24)|r7_relat_2(X20,X24)|~v1_relat_1(X20)))&(~r2_hidden(k4_tarski(esk2_2(X20,X24),esk3_2(X20,X24)),X20)|r7_relat_2(X20,X24)|~v1_relat_1(X20)))&(~r2_hidden(k4_tarski(esk3_2(X20,X24),esk2_2(X20,X24)),X20)|r7_relat_2(X20,X24)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).
% 0.43/0.60  cnf(c_0_44, plain, (v6_orders_2(X2,X1)|~r7_relat_2(u1_orders_2(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.43/0.60  cnf(c_0_45, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk5_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.43/0.60  cnf(c_0_46, plain, (v1_xboole_0(X1)|r2_hidden(X2,k6_domain_1(X1,X2))|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_22])).
% 0.43/0.60  cnf(c_0_47, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v6_orders_2(k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29])])).
% 0.43/0.60  cnf(c_0_48, plain, (r2_hidden(esk2_2(X1,X2),X2)|r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.43/0.60  cnf(c_0_49, plain, (v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)|v1_xboole_0(u1_struct_0(X1))|~r7_relat_2(u1_orders_2(X1),k6_domain_1(u1_struct_0(X1),X2))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.43/0.60  cnf(c_0_50, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk5_0)=k2_tarski(esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_29])])).
% 0.43/0.60  cnf(c_0_51, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.60  cnf(c_0_52, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v6_orders_2(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_22]), c_0_29])])).
% 0.43/0.60  cnf(c_0_53, plain, (r2_hidden(esk3_2(X1,X2),X2)|r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.43/0.60  cnf(c_0_54, plain, (r7_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.43/0.60  cnf(c_0_55, plain, (esk2_2(X1,k2_tarski(X2,X2))=X2|r7_relat_2(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_48])).
% 0.43/0.60  cnf(c_0_56, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_29])]), c_0_52])).
% 0.43/0.60  cnf(c_0_57, plain, (esk3_2(X1,k2_tarski(X2,X2))=X2|r7_relat_2(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_53])).
% 0.43/0.60  cnf(c_0_58, plain, (r7_relat_2(X1,k2_tarski(X2,X2))|~v1_relat_1(X1)|~r2_hidden(k4_tarski(X2,esk3_2(X1,k2_tarski(X2,X2))),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.43/0.60  cnf(c_0_59, negated_conjecture, (esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|~v1_relat_1(u1_orders_2(esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.43/0.60  fof(c_0_60, plain, ![X27, X28, X29]:((~r1_orders_2(X27,X28,X29)|r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))&(~r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))|r1_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.43/0.60  cnf(c_0_61, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v1_relat_1(u1_orders_2(esk4_0))|~r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_56])).
% 0.43/0.60  cnf(c_0_62, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.43/0.60  fof(c_0_63, plain, ![X36, X37]:(v2_struct_0(X36)|~v3_orders_2(X36)|~l1_orders_2(X36)|(~m1_subset_1(X37,u1_struct_0(X36))|r1_orders_2(X36,X37,X37))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.43/0.60  fof(c_0_64, plain, ![X17]:(v2_struct_0(X17)|~l1_struct_0(X17)|~v1_xboole_0(u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.43/0.60  cnf(c_0_65, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r1_orders_2(esk4_0,esk5_0,esk5_0)|~v1_relat_1(u1_orders_2(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_51]), c_0_29])])).
% 0.43/0.60  cnf(c_0_66, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.43/0.60  cnf(c_0_67, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.60  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.43/0.60  fof(c_0_69, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.43/0.60  fof(c_0_70, plain, ![X33]:(~l1_orders_2(X33)|m1_subset_1(u1_orders_2(X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.43/0.60  fof(c_0_71, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.43/0.60  cnf(c_0_72, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.43/0.60  cnf(c_0_73, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~v1_relat_1(u1_orders_2(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67]), c_0_51]), c_0_29])]), c_0_68])).
% 0.43/0.60  cnf(c_0_74, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.43/0.60  cnf(c_0_75, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.43/0.60  cnf(c_0_76, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.43/0.60  cnf(c_0_77, negated_conjecture, (~l1_struct_0(esk4_0)|~v1_relat_1(u1_orders_2(esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_68])).
% 0.43/0.60  cnf(c_0_78, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76])])).
% 0.43/0.60  fof(c_0_79, plain, ![X32]:(~l1_orders_2(X32)|l1_struct_0(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.43/0.60  cnf(c_0_80, negated_conjecture, (~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_51])])).
% 0.43/0.60  cnf(c_0_81, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.43/0.60  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_51])]), ['proof']).
% 0.43/0.60  # SZS output end CNFRefutation
% 0.43/0.60  # Proof object total steps             : 83
% 0.43/0.60  # Proof object clause steps            : 54
% 0.43/0.60  # Proof object formula steps           : 29
% 0.43/0.60  # Proof object conjectures             : 23
% 0.43/0.60  # Proof object clause conjectures      : 20
% 0.43/0.60  # Proof object formula conjectures     : 3
% 0.43/0.60  # Proof object initial clauses used    : 23
% 0.43/0.60  # Proof object initial formulas used   : 14
% 0.43/0.60  # Proof object generating inferences   : 25
% 0.43/0.60  # Proof object simplifying inferences  : 32
% 0.43/0.60  # Training examples: 0 positive, 0 negative
% 0.43/0.60  # Parsed axioms                        : 14
% 0.43/0.60  # Removed by relevancy pruning/SinE    : 0
% 0.43/0.60  # Initial clauses                      : 27
% 0.43/0.60  # Removed in clause preprocessing      : 1
% 0.43/0.60  # Initial clauses in saturation        : 26
% 0.43/0.60  # Processed clauses                    : 703
% 0.43/0.60  # ...of these trivial                  : 4
% 0.43/0.60  # ...subsumed                          : 323
% 0.43/0.60  # ...remaining for further processing  : 376
% 0.43/0.60  # Other redundant clauses eliminated   : 75
% 0.43/0.60  # Clauses deleted for lack of memory   : 0
% 0.43/0.60  # Backward-subsumed                    : 24
% 0.43/0.60  # Backward-rewritten                   : 0
% 0.43/0.60  # Generated clauses                    : 6308
% 0.43/0.60  # ...of the previous two non-trivial   : 6000
% 0.43/0.60  # Contextual simplify-reflections      : 10
% 0.43/0.60  # Paramodulations                      : 6195
% 0.43/0.60  # Factorizations                       : 24
% 0.43/0.60  # Equation resolutions                 : 89
% 0.43/0.60  # Propositional unsat checks           : 0
% 0.43/0.60  #    Propositional check models        : 0
% 0.43/0.60  #    Propositional check unsatisfiable : 0
% 0.43/0.60  #    Propositional clauses             : 0
% 0.43/0.60  #    Propositional clauses after purity: 0
% 0.43/0.60  #    Propositional unsat core size     : 0
% 0.43/0.60  #    Propositional preprocessing time  : 0.000
% 0.43/0.60  #    Propositional encoding time       : 0.000
% 0.43/0.60  #    Propositional solver time         : 0.000
% 0.43/0.60  #    Success case prop preproc time    : 0.000
% 0.43/0.60  #    Success case prop encoding time   : 0.000
% 0.43/0.60  #    Success case prop solver time     : 0.000
% 0.43/0.60  # Current number of processed clauses  : 325
% 0.43/0.60  #    Positive orientable unit clauses  : 5
% 0.43/0.60  #    Positive unorientable unit clauses: 0
% 0.43/0.60  #    Negative unit clauses             : 2
% 0.43/0.60  #    Non-unit-clauses                  : 318
% 0.43/0.60  # Current number of unprocessed clauses: 5292
% 0.43/0.60  # ...number of literals in the above   : 44600
% 0.43/0.60  # Current number of archived formulas  : 0
% 0.43/0.60  # Current number of archived clauses   : 51
% 0.43/0.60  # Clause-clause subsumption calls (NU) : 39297
% 0.43/0.60  # Rec. Clause-clause subsumption calls : 4146
% 0.43/0.60  # Non-unit clause-clause subsumptions  : 357
% 0.43/0.60  # Unit Clause-clause subsumption calls : 237
% 0.43/0.60  # Rewrite failures with RHS unbound    : 0
% 0.43/0.60  # BW rewrite match attempts            : 1
% 0.43/0.60  # BW rewrite match successes           : 0
% 0.43/0.60  # Condensation attempts                : 0
% 0.43/0.60  # Condensation successes               : 0
% 0.43/0.60  # Termbank termtop insertions          : 182041
% 0.43/0.60  
% 0.43/0.60  # -------------------------------------------------
% 0.43/0.60  # User time                : 0.245 s
% 0.43/0.60  # System time              : 0.008 s
% 0.43/0.60  # Total time               : 0.253 s
% 0.43/0.60  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
