%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:32 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 427 expanded)
%              Number of clauses        :   72 ( 183 expanded)
%              Number of leaves         :   16 ( 106 expanded)
%              Depth                    :   21
%              Number of atoms          :  336 (1533 expanded)
%              Number of equality atoms :   56 ( 157 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
              & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_orders_2])).

fof(c_0_17,plain,(
    ! [X49,X50] :
      ( v1_xboole_0(X49)
      | ~ m1_subset_1(X50,X49)
      | k6_domain_1(X49,X50) = k1_tarski(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_18,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_19,plain,(
    ! [X45,X46] :
      ( v1_xboole_0(X45)
      | ~ m1_subset_1(X46,X45)
      | m1_subset_1(k6_domain_1(X45,X46),k1_zfmisc_1(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk6_0),esk7_0),esk6_0)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(X22))
      | ~ r2_hidden(X24,X23)
      | r2_hidden(X24,X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | ~ v1_xboole_0(u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_27,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_28,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | v1_relat_1(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_29,plain,(
    ! [X48] :
      ( ~ l1_orders_2(X48)
      | m1_subset_1(u1_orders_2(X48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X48)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_30,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_31,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k2_tarski(esk7_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_36,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ r1_relat_2(X29,X30)
        | ~ r2_hidden(X31,X30)
        | r2_hidden(k4_tarski(X31,X31),X29)
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(esk3_2(X29,X32),X32)
        | r1_relat_2(X29,X32)
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X29,X32),esk3_2(X29,X32)),X29)
        | r1_relat_2(X29,X32)
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_37,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk6_0),esk7_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k2_tarski(esk7_0,esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

fof(c_0_42,plain,(
    ! [X47] :
      ( ~ l1_orders_2(X47)
      | l1_struct_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_43,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X15,X14)
        | X15 = X12
        | X15 = X13
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X12
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( X16 != X13
        | r2_hidden(X16,X14)
        | X14 != k2_tarski(X12,X13) )
      & ( esk2_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk2_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X19)
        | esk2_3(X17,X18,X19) = X17
        | esk2_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_44,plain,(
    ! [X37] :
      ( ( ~ v3_orders_2(X37)
        | r1_relat_2(u1_orders_2(X37),u1_struct_0(X37))
        | ~ l1_orders_2(X37) )
      & ( ~ r1_relat_2(u1_orders_2(X37),u1_struct_0(X37))
        | v3_orders_2(X37)
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r1_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_46,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0)
    | ~ r2_hidden(X1,k2_tarski(esk7_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( r1_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk3_2(u1_orders_2(X1),X2),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,k2_tarski(esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).

cnf(c_0_57,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk3_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_46])).

cnf(c_0_59,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk6_0),X1)
    | r2_hidden(esk3_2(u1_orders_2(esk6_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_49])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_62,plain,(
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

fof(c_0_63,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( ~ r7_relat_2(X38,X39)
        | ~ r2_hidden(X40,X39)
        | ~ r2_hidden(X41,X39)
        | r2_hidden(k4_tarski(X40,X41),X38)
        | r2_hidden(k4_tarski(X41,X40),X38)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(esk4_2(X38,X42),X42)
        | r7_relat_2(X38,X42)
        | ~ v1_relat_1(X38) )
      & ( r2_hidden(esk5_2(X38,X42),X42)
        | r7_relat_2(X38,X42)
        | ~ v1_relat_1(X38) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X38,X42),esk5_2(X38,X42)),X38)
        | r7_relat_2(X38,X42)
        | ~ v1_relat_1(X38) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X38,X42),esk4_2(X38,X42)),X38)
        | r7_relat_2(X38,X42)
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_64,plain,
    ( r1_relat_2(u1_orders_2(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ r2_hidden(esk3_2(u1_orders_2(X1),X2),u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_46])).

cnf(c_0_65,negated_conjecture,
    ( esk3_2(u1_orders_2(esk6_0),k2_tarski(X1,X2)) = X2
    | esk3_2(u1_orders_2(esk6_0),k2_tarski(X1,X2)) = X1
    | r1_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_61]),c_0_35])).

cnf(c_0_68,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( esk3_2(u1_orders_2(esk6_0),k2_tarski(X1,X2)) = X2
    | r1_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X2))
    | ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),c_0_49])])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_48]),c_0_49])])).

cnf(c_0_72,plain,
    ( X1 = X3
    | X2 != k2_tarski(X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_68,c_0_22])).

cnf(c_0_73,plain,
    ( r7_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk4_2(u1_orders_2(X1),X2),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_46])).

cnf(c_0_74,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_75,negated_conjecture,
    ( esk3_2(u1_orders_2(esk6_0),k2_tarski(esk7_0,X1)) = X1
    | r1_relat_2(u1_orders_2(esk6_0),k2_tarski(esk7_0,X1)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk6_0),X1)
    | r2_hidden(esk4_2(u1_orders_2(esk6_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_49])).

cnf(c_0_78,plain,
    ( r7_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk5_2(u1_orders_2(X1),X2),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_46])).

cnf(c_0_79,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk6_0),k2_tarski(esk7_0,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_75]),c_0_66]),c_0_49])])).

cnf(c_0_80,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( esk4_2(u1_orders_2(esk6_0),k2_tarski(X1,X1)) = X1
    | r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk6_0),X1)
    | r2_hidden(esk5_2(u1_orders_2(esk6_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_49])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0))
    | ~ v1_relat_1(u1_orders_2(esk6_0))
    | ~ r2_hidden(X1,k2_tarski(esk7_0,X2))
    | ~ r2_hidden(X2,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_79])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_85,plain,(
    ! [X35,X36] :
      ( ( ~ v6_orders_2(X36,X35)
        | r7_relat_2(u1_orders_2(X35),X36)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) )
      & ( ~ r7_relat_2(u1_orders_2(X35),X36)
        | v6_orders_2(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_86,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))
    | ~ v1_relat_1(u1_orders_2(esk6_0))
    | ~ r2_hidden(k4_tarski(X1,esk5_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))),u1_orders_2(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( esk5_2(u1_orders_2(esk6_0),k2_tarski(X1,X1)) = X1
    | r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0))
    | ~ r2_hidden(X1,k2_tarski(esk7_0,X2))
    | ~ r2_hidden(X2,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_46]),c_0_49])])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).

cnf(c_0_90,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_91,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))
    | ~ v1_relat_1(u1_orders_2(esk6_0))
    | ~ r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_41])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk6_0))
    | ~ r2_hidden(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk6_0),esk7_0),esk6_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( v6_orders_2(k2_tarski(X1,X1),esk6_0)
    | ~ v1_relat_1(u1_orders_2(esk6_0))
    | ~ m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_49])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_48]),c_0_49])])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_71])).

cnf(c_0_98,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(esk6_0),esk7_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_32])).

cnf(c_0_99,negated_conjecture,
    ( v6_orders_2(k2_tarski(esk7_0,esk7_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v1_relat_1(u1_orders_2(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_97])])).

cnf(c_0_100,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ v6_orders_2(k2_tarski(esk7_0,esk7_0),esk6_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_41])).

cnf(c_0_101,negated_conjecture,
    ( v6_orders_2(k2_tarski(esk7_0,esk7_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_46]),c_0_49])])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_103,negated_conjecture,
    ( ~ l1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_102]),c_0_35])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_48]),c_0_49])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.46/1.65  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 1.46/1.65  # and selection function SelectComplexExceptUniqMaxHorn.
% 1.46/1.65  #
% 1.46/1.65  # Preprocessing time       : 0.047 s
% 1.46/1.65  # Presaturation interreduction done
% 1.46/1.65  
% 1.46/1.65  # Proof found!
% 1.46/1.65  # SZS status Theorem
% 1.46/1.65  # SZS output start CNFRefutation
% 1.46/1.65  fof(t35_orders_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_orders_2)).
% 1.46/1.65  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 1.46/1.65  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.46/1.65  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.46/1.65  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.46/1.65  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.46/1.65  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.46/1.65  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 1.46/1.65  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.46/1.65  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 1.46/1.65  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 1.46/1.65  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.46/1.65  fof(d4_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v3_orders_2(X1)<=>r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 1.46/1.65  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.46/1.65  fof(d7_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r7_relat_2(X1,X2)<=>![X3, X4]:~((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&~(r2_hidden(k4_tarski(X3,X4),X1)))&~(r2_hidden(k4_tarski(X4,X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_relat_2)).
% 1.46/1.65  fof(d11_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v6_orders_2(X2,X1)<=>r7_relat_2(u1_orders_2(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_orders_2)).
% 1.46/1.65  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t35_orders_2])).
% 1.46/1.65  fof(c_0_17, plain, ![X49, X50]:(v1_xboole_0(X49)|~m1_subset_1(X50,X49)|k6_domain_1(X49,X50)=k1_tarski(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 1.46/1.65  fof(c_0_18, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.46/1.65  fof(c_0_19, plain, ![X45, X46]:(v1_xboole_0(X45)|~m1_subset_1(X46,X45)|m1_subset_1(k6_domain_1(X45,X46),k1_zfmisc_1(X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 1.46/1.65  fof(c_0_20, negated_conjecture, (((~v2_struct_0(esk6_0)&v3_orders_2(esk6_0))&l1_orders_2(esk6_0))&(m1_subset_1(esk7_0,u1_struct_0(esk6_0))&(~v6_orders_2(k6_domain_1(u1_struct_0(esk6_0),esk7_0),esk6_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 1.46/1.65  cnf(c_0_21, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 1.46/1.65  cnf(c_0_22, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.46/1.65  fof(c_0_23, plain, ![X22, X23, X24]:(~m1_subset_1(X23,k1_zfmisc_1(X22))|(~r2_hidden(X24,X23)|r2_hidden(X24,X22))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 1.46/1.65  cnf(c_0_24, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.46/1.65  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.46/1.65  fof(c_0_26, plain, ![X34]:(v2_struct_0(X34)|~l1_struct_0(X34)|~v1_xboole_0(u1_struct_0(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 1.46/1.65  cnf(c_0_27, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 1.46/1.65  fof(c_0_28, plain, ![X25, X26]:(~v1_relat_1(X25)|(~m1_subset_1(X26,k1_zfmisc_1(X25))|v1_relat_1(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.46/1.65  fof(c_0_29, plain, ![X48]:(~l1_orders_2(X48)|m1_subset_1(u1_orders_2(X48),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X48))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 1.46/1.65  fof(c_0_30, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.46/1.65  cnf(c_0_31, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.46/1.65  cnf(c_0_32, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 1.46/1.65  cnf(c_0_33, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.46/1.65  cnf(c_0_34, negated_conjecture, (k6_domain_1(u1_struct_0(esk6_0),esk7_0)=k2_tarski(esk7_0,esk7_0)|v1_xboole_0(u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_25])).
% 1.46/1.65  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.46/1.65  fof(c_0_36, plain, ![X29, X30, X31, X32]:((~r1_relat_2(X29,X30)|(~r2_hidden(X31,X30)|r2_hidden(k4_tarski(X31,X31),X29))|~v1_relat_1(X29))&((r2_hidden(esk3_2(X29,X32),X32)|r1_relat_2(X29,X32)|~v1_relat_1(X29))&(~r2_hidden(k4_tarski(esk3_2(X29,X32),esk3_2(X29,X32)),X29)|r1_relat_2(X29,X32)|~v1_relat_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 1.46/1.65  cnf(c_0_37, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.46/1.65  cnf(c_0_38, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.46/1.65  cnf(c_0_39, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.46/1.65  cnf(c_0_40, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk6_0),esk7_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.46/1.65  cnf(c_0_41, negated_conjecture, (k6_domain_1(u1_struct_0(esk6_0),esk7_0)=k2_tarski(esk7_0,esk7_0)|~l1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 1.46/1.65  fof(c_0_42, plain, ![X47]:(~l1_orders_2(X47)|l1_struct_0(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 1.46/1.65  fof(c_0_43, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X15,X14)|(X15=X12|X15=X13)|X14!=k2_tarski(X12,X13))&((X16!=X12|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))&(X16!=X13|r2_hidden(X16,X14)|X14!=k2_tarski(X12,X13))))&(((esk2_3(X17,X18,X19)!=X17|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18))&(esk2_3(X17,X18,X19)!=X18|~r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k2_tarski(X17,X18)))&(r2_hidden(esk2_3(X17,X18,X19),X19)|(esk2_3(X17,X18,X19)=X17|esk2_3(X17,X18,X19)=X18)|X19=k2_tarski(X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 1.46/1.65  fof(c_0_44, plain, ![X37]:((~v3_orders_2(X37)|r1_relat_2(u1_orders_2(X37),u1_struct_0(X37))|~l1_orders_2(X37))&(~r1_relat_2(u1_orders_2(X37),u1_struct_0(X37))|v3_orders_2(X37)|~l1_orders_2(X37))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).
% 1.46/1.65  cnf(c_0_45, plain, (r2_hidden(esk3_2(X1,X2),X2)|r1_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.46/1.65  cnf(c_0_46, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])])).
% 1.46/1.65  cnf(c_0_47, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(X1,u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)|~r2_hidden(X1,k2_tarski(esk7_0,esk7_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 1.46/1.65  cnf(c_0_48, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 1.46/1.65  cnf(c_0_49, negated_conjecture, (l1_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.46/1.65  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.46/1.65  cnf(c_0_51, plain, (r2_hidden(k4_tarski(X3,X3),X1)|~r1_relat_2(X1,X2)|~r2_hidden(X3,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.46/1.65  cnf(c_0_52, plain, (r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.46/1.65  cnf(c_0_53, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.46/1.65  cnf(c_0_54, plain, (r1_relat_2(u1_orders_2(X1),X2)|r2_hidden(esk3_2(u1_orders_2(X1),X2),X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.46/1.65  cnf(c_0_55, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,k2_tarski(esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 1.46/1.65  cnf(c_0_56, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_50])])).
% 1.46/1.65  cnf(c_0_57, plain, (r1_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk3_2(X1,X2),esk3_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.46/1.65  cnf(c_0_58, plain, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)|~r2_hidden(X1,u1_struct_0(X2))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_46])).
% 1.46/1.65  cnf(c_0_59, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_53])).
% 1.46/1.65  cnf(c_0_60, negated_conjecture, (r1_relat_2(u1_orders_2(esk6_0),X1)|r2_hidden(esk3_2(u1_orders_2(esk6_0),X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_49])).
% 1.46/1.65  cnf(c_0_61, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 1.46/1.65  fof(c_0_62, plain, ![X5, X6, X7, X8, X9, X10]:(((~r2_hidden(X7,X6)|X7=X5|X6!=k1_tarski(X5))&(X8!=X5|r2_hidden(X8,X6)|X6!=k1_tarski(X5)))&((~r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)!=X9|X10=k1_tarski(X9))&(r2_hidden(esk1_2(X9,X10),X10)|esk1_2(X9,X10)=X9|X10=k1_tarski(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.46/1.65  fof(c_0_63, plain, ![X38, X39, X40, X41, X42]:((~r7_relat_2(X38,X39)|(~r2_hidden(X40,X39)|~r2_hidden(X41,X39)|r2_hidden(k4_tarski(X40,X41),X38)|r2_hidden(k4_tarski(X41,X40),X38))|~v1_relat_1(X38))&((((r2_hidden(esk4_2(X38,X42),X42)|r7_relat_2(X38,X42)|~v1_relat_1(X38))&(r2_hidden(esk5_2(X38,X42),X42)|r7_relat_2(X38,X42)|~v1_relat_1(X38)))&(~r2_hidden(k4_tarski(esk4_2(X38,X42),esk5_2(X38,X42)),X38)|r7_relat_2(X38,X42)|~v1_relat_1(X38)))&(~r2_hidden(k4_tarski(esk5_2(X38,X42),esk4_2(X38,X42)),X38)|r7_relat_2(X38,X42)|~v1_relat_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).
% 1.46/1.65  cnf(c_0_64, plain, (r1_relat_2(u1_orders_2(X1),X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~r2_hidden(esk3_2(u1_orders_2(X1),X2),u1_struct_0(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_46])).
% 1.46/1.65  cnf(c_0_65, negated_conjecture, (esk3_2(u1_orders_2(esk6_0),k2_tarski(X1,X2))=X2|esk3_2(u1_orders_2(esk6_0),k2_tarski(X1,X2))=X1|r1_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 1.46/1.65  cnf(c_0_66, negated_conjecture, (v3_orders_2(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.46/1.65  cnf(c_0_67, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_61]), c_0_35])).
% 1.46/1.65  cnf(c_0_68, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.46/1.65  cnf(c_0_69, plain, (r2_hidden(esk4_2(X1,X2),X2)|r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.46/1.65  cnf(c_0_70, negated_conjecture, (esk3_2(u1_orders_2(esk6_0),k2_tarski(X1,X2))=X2|r1_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X2))|~r2_hidden(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66]), c_0_49])])).
% 1.46/1.65  cnf(c_0_71, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_48]), c_0_49])])).
% 1.46/1.65  cnf(c_0_72, plain, (X1=X3|X2!=k2_tarski(X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_68, c_0_22])).
% 1.46/1.65  cnf(c_0_73, plain, (r7_relat_2(u1_orders_2(X1),X2)|r2_hidden(esk4_2(u1_orders_2(X1),X2),X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_69, c_0_46])).
% 1.46/1.65  cnf(c_0_74, plain, (r2_hidden(esk5_2(X1,X2),X2)|r7_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.46/1.65  cnf(c_0_75, negated_conjecture, (esk3_2(u1_orders_2(esk6_0),k2_tarski(esk7_0,X1))=X1|r1_relat_2(u1_orders_2(esk6_0),k2_tarski(esk7_0,X1))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.46/1.65  cnf(c_0_76, plain, (X1=X2|~r2_hidden(X1,k2_tarski(X2,X2))), inference(er,[status(thm)],[c_0_72])).
% 1.46/1.65  cnf(c_0_77, negated_conjecture, (r7_relat_2(u1_orders_2(esk6_0),X1)|r2_hidden(esk4_2(u1_orders_2(esk6_0),X1),X1)), inference(spm,[status(thm)],[c_0_73, c_0_49])).
% 1.46/1.65  cnf(c_0_78, plain, (r7_relat_2(u1_orders_2(X1),X2)|r2_hidden(esk5_2(u1_orders_2(X1),X2),X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_74, c_0_46])).
% 1.46/1.65  cnf(c_0_79, negated_conjecture, (r1_relat_2(u1_orders_2(esk6_0),k2_tarski(esk7_0,X1))|~r2_hidden(X1,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_75]), c_0_66]), c_0_49])])).
% 1.46/1.65  cnf(c_0_80, plain, (r7_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 1.46/1.65  cnf(c_0_81, negated_conjecture, (esk4_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))=X1|r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 1.46/1.65  cnf(c_0_82, negated_conjecture, (r7_relat_2(u1_orders_2(esk6_0),X1)|r2_hidden(esk5_2(u1_orders_2(esk6_0),X1),X1)), inference(spm,[status(thm)],[c_0_78, c_0_49])).
% 1.46/1.65  cnf(c_0_83, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0))|~v1_relat_1(u1_orders_2(esk6_0))|~r2_hidden(X1,k2_tarski(esk7_0,X2))|~r2_hidden(X2,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_79])).
% 1.46/1.65  cnf(c_0_84, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.46/1.65  fof(c_0_85, plain, ![X35, X36]:((~v6_orders_2(X36,X35)|r7_relat_2(u1_orders_2(X35),X36)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35))&(~r7_relat_2(u1_orders_2(X35),X36)|v6_orders_2(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|~l1_orders_2(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).
% 1.46/1.65  cnf(c_0_86, negated_conjecture, (r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))|~v1_relat_1(u1_orders_2(esk6_0))|~r2_hidden(k4_tarski(X1,esk5_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))),u1_orders_2(esk6_0))), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 1.46/1.65  cnf(c_0_87, negated_conjecture, (esk5_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))=X1|r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_76, c_0_82])).
% 1.46/1.65  cnf(c_0_88, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0))|~r2_hidden(X1,k2_tarski(esk7_0,X2))|~r2_hidden(X2,u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_46]), c_0_49])])).
% 1.46/1.65  cnf(c_0_89, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_84])])).
% 1.46/1.65  cnf(c_0_90, plain, (v6_orders_2(X2,X1)|~r7_relat_2(u1_orders_2(X1),X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.46/1.65  cnf(c_0_91, negated_conjecture, (r7_relat_2(u1_orders_2(esk6_0),k2_tarski(X1,X1))|~v1_relat_1(u1_orders_2(esk6_0))|~r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 1.46/1.65  cnf(c_0_92, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_32, c_0_41])).
% 1.46/1.65  cnf(c_0_93, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk6_0))|~r2_hidden(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 1.46/1.65  cnf(c_0_94, negated_conjecture, (~v6_orders_2(k6_domain_1(u1_struct_0(esk6_0),esk7_0),esk6_0)|~m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.46/1.65  cnf(c_0_95, negated_conjecture, (v6_orders_2(k2_tarski(X1,X1),esk6_0)|~v1_relat_1(u1_orders_2(esk6_0))|~m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))|~r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_49])])).
% 1.46/1.65  cnf(c_0_96, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|m1_subset_1(k2_tarski(esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_48]), c_0_49])])).
% 1.46/1.65  cnf(c_0_97, negated_conjecture, (r2_hidden(k4_tarski(esk7_0,esk7_0),u1_orders_2(esk6_0))), inference(spm,[status(thm)],[c_0_93, c_0_71])).
% 1.46/1.65  cnf(c_0_98, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~v6_orders_2(k6_domain_1(u1_struct_0(esk6_0),esk7_0),esk6_0)), inference(spm,[status(thm)],[c_0_94, c_0_32])).
% 1.46/1.65  cnf(c_0_99, negated_conjecture, (v6_orders_2(k2_tarski(esk7_0,esk7_0),esk6_0)|v1_xboole_0(u1_struct_0(esk6_0))|~v1_relat_1(u1_orders_2(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_97])])).
% 1.46/1.65  cnf(c_0_100, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~v6_orders_2(k2_tarski(esk7_0,esk7_0),esk6_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_98, c_0_41])).
% 1.46/1.65  cnf(c_0_101, negated_conjecture, (v6_orders_2(k2_tarski(esk7_0,esk7_0),esk6_0)|v1_xboole_0(u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_46]), c_0_49])])).
% 1.46/1.65  cnf(c_0_102, negated_conjecture, (v1_xboole_0(u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 1.46/1.65  cnf(c_0_103, negated_conjecture, (~l1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_102]), c_0_35])).
% 1.46/1.65  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_48]), c_0_49])]), ['proof']).
% 1.46/1.65  # SZS output end CNFRefutation
% 1.46/1.65  # Proof object total steps             : 105
% 1.46/1.65  # Proof object clause steps            : 72
% 1.46/1.65  # Proof object formula steps           : 33
% 1.46/1.65  # Proof object conjectures             : 42
% 1.46/1.65  # Proof object clause conjectures      : 39
% 1.46/1.65  # Proof object formula conjectures     : 3
% 1.46/1.65  # Proof object initial clauses used    : 26
% 1.46/1.65  # Proof object initial formulas used   : 16
% 1.46/1.65  # Proof object generating inferences   : 40
% 1.46/1.65  # Proof object simplifying inferences  : 37
% 1.46/1.65  # Training examples: 0 positive, 0 negative
% 1.46/1.65  # Parsed axioms                        : 16
% 1.46/1.65  # Removed by relevancy pruning/SinE    : 0
% 1.46/1.65  # Initial clauses                      : 36
% 1.46/1.65  # Removed in clause preprocessing      : 1
% 1.46/1.65  # Initial clauses in saturation        : 35
% 1.46/1.65  # Processed clauses                    : 2506
% 1.46/1.65  # ...of these trivial                  : 3
% 1.46/1.65  # ...subsumed                          : 1153
% 1.46/1.65  # ...remaining for further processing  : 1350
% 1.46/1.65  # Other redundant clauses eliminated   : 259
% 1.46/1.65  # Clauses deleted for lack of memory   : 0
% 1.46/1.65  # Backward-subsumed                    : 242
% 1.46/1.65  # Backward-rewritten                   : 10
% 1.46/1.65  # Generated clauses                    : 58598
% 1.46/1.65  # ...of the previous two non-trivial   : 56565
% 1.46/1.65  # Contextual simplify-reflections      : 10
% 1.46/1.65  # Paramodulations                      : 58236
% 1.46/1.65  # Factorizations                       : 106
% 1.46/1.65  # Equation resolutions                 : 259
% 1.46/1.65  # Propositional unsat checks           : 0
% 1.46/1.65  #    Propositional check models        : 0
% 1.46/1.65  #    Propositional check unsatisfiable : 0
% 1.46/1.65  #    Propositional clauses             : 0
% 1.46/1.65  #    Propositional clauses after purity: 0
% 1.46/1.65  #    Propositional unsat core size     : 0
% 1.46/1.65  #    Propositional preprocessing time  : 0.000
% 1.46/1.65  #    Propositional encoding time       : 0.000
% 1.46/1.65  #    Propositional solver time         : 0.000
% 1.46/1.65  #    Success case prop preproc time    : 0.000
% 1.46/1.65  #    Success case prop encoding time   : 0.000
% 1.46/1.65  #    Success case prop solver time     : 0.000
% 1.46/1.65  # Current number of processed clauses  : 1059
% 1.46/1.65  #    Positive orientable unit clauses  : 13
% 1.46/1.65  #    Positive unorientable unit clauses: 0
% 1.46/1.65  #    Negative unit clauses             : 2
% 1.46/1.65  #    Non-unit-clauses                  : 1044
% 1.46/1.65  # Current number of unprocessed clauses: 53976
% 1.46/1.65  # ...number of literals in the above   : 404419
% 1.46/1.65  # Current number of archived formulas  : 0
% 1.46/1.65  # Current number of archived clauses   : 287
% 1.46/1.65  # Clause-clause subsumption calls (NU) : 335859
% 1.46/1.65  # Rec. Clause-clause subsumption calls : 21581
% 1.46/1.65  # Non-unit clause-clause subsumptions  : 1393
% 1.46/1.65  # Unit Clause-clause subsumption calls : 1732
% 1.46/1.65  # Rewrite failures with RHS unbound    : 0
% 1.46/1.65  # BW rewrite match attempts            : 9
% 1.46/1.65  # BW rewrite match successes           : 5
% 1.46/1.65  # Condensation attempts                : 0
% 1.46/1.65  # Condensation successes               : 0
% 1.46/1.65  # Termbank termtop insertions          : 2218778
% 1.46/1.66  
% 1.46/1.66  # -------------------------------------------------
% 1.46/1.66  # User time                : 1.266 s
% 1.46/1.66  # System time              : 0.039 s
% 1.46/1.66  # Total time               : 1.305 s
% 1.46/1.66  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
