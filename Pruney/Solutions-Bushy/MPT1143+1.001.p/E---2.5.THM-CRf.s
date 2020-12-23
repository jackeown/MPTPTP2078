%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1143+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:48 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 224 expanded)
%              Number of clauses        :   41 (  93 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 817 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
              & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_orders_2])).

fof(c_0_14,plain,(
    ! [X33] :
      ( ~ l1_orders_2(X33)
      | m1_subset_1(u1_orders_2(X33),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X33)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0)
      | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X32] :
      ( ~ l1_orders_2(X32)
      | l1_struct_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_17,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X34] :
      ( v2_struct_0(X34)
      | ~ l1_struct_0(X34)
      | ~ v1_xboole_0(u1_struct_0(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_21,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X15
        | X16 != k1_tarski(X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_tarski(X15) )
      & ( ~ r2_hidden(esk2_2(X19,X20),X20)
        | esk2_2(X19,X20) != X19
        | X20 = k1_tarski(X19) )
      & ( r2_hidden(esk2_2(X19,X20),X20)
        | esk2_2(X19,X20) = X19
        | X20 = k1_tarski(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_23,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( ( ~ r7_relat_2(X23,X24)
        | ~ r2_hidden(X25,X24)
        | ~ r2_hidden(X26,X24)
        | r2_hidden(k4_tarski(X25,X26),X23)
        | r2_hidden(k4_tarski(X26,X25),X23)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk3_2(X23,X27),X27)
        | r7_relat_2(X23,X27)
        | ~ v1_relat_1(X23) )
      & ( r2_hidden(esk4_2(X23,X27),X27)
        | r7_relat_2(X23,X27)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X23,X27),esk4_2(X23,X27)),X23)
        | r7_relat_2(X23,X27)
        | ~ v1_relat_1(X23) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X23,X27),esk3_2(X23,X27)),X23)
        | r7_relat_2(X23,X27)
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | m1_subset_1(k6_domain_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_33,plain,(
    ! [X22] :
      ( ( ~ v3_orders_2(X22)
        | r1_relat_2(u1_orders_2(X22),u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_relat_2(u1_orders_2(X22),u1_struct_0(X22))
        | v3_orders_2(X22)
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

fof(c_0_34,plain,(
    ! [X35,X36] :
      ( v1_xboole_0(X35)
      | ~ m1_subset_1(X36,X35)
      | k6_domain_1(X35,X36) = k1_tarski(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk3_2(u1_orders_2(esk5_0),X1),X1)
    | r7_relat_2(u1_orders_2(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_41,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r1_relat_2(X10,X11)
        | ~ r2_hidden(X12,X11)
        | r2_hidden(k4_tarski(X12,X12),X10)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(esk1_2(X10,X13),X13)
        | r1_relat_2(X10,X13)
        | ~ v1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X10,X13),esk1_2(X10,X13)),X10)
        | r1_relat_2(X10,X13)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_42,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_44,plain,(
    ! [X37,X38] :
      ( ~ m1_subset_1(X37,X38)
      | v1_xboole_0(X38)
      | r2_hidden(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_48,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( esk3_2(u1_orders_2(esk5_0),k1_tarski(X1)) = X1
    | r7_relat_2(u1_orders_2(esk5_0),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk4_2(u1_orders_2(esk5_0),X1),X1)
    | r7_relat_2(u1_orders_2(esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_32])).

cnf(c_0_51,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_43])])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_54,plain,(
    ! [X8,X9] :
      ( ( ~ v6_orders_2(X9,X8)
        | r7_relat_2(u1_orders_2(X8),X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) )
      & ( ~ r7_relat_2(u1_orders_2(X8),X9)
        | v6_orders_2(X9,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_55,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk6_0) = k1_tarski(esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(esk5_0),esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk5_0),k1_tarski(X1))
    | ~ r2_hidden(k4_tarski(X1,esk4_2(u1_orders_2(esk5_0),k1_tarski(X1))),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_32])])).

cnf(c_0_58,negated_conjecture,
    ( esk4_2(u1_orders_2(esk5_0),k1_tarski(X1)) = X1
    | r7_relat_2(u1_orders_2(esk5_0),k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_32])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_36]),c_0_37])).

cnf(c_0_61,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(rw,[status(thm)],[c_0_47,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( ~ v6_orders_2(k1_tarski(esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk5_0),k1_tarski(X1))
    | ~ r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( ~ r7_relat_2(u1_orders_2(esk5_0),k1_tarski(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_19])]),c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66]),
    [proof]).

%------------------------------------------------------------------------------
