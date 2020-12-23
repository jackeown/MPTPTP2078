%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1144+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:48 EST 2020

% Result     : Theorem 0.50s
% Output     : CNFRefutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  159 (9623 expanded)
%              Number of clauses        :  130 (3940 expanded)
%              Number of leaves         :   14 (2277 expanded)
%              Depth                    :   30
%              Number of atoms          :  561 (61651 expanded)
%              Number of equality atoms :   63 (2882 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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

fof(t36_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v6_orders_2(k7_domain_1(u1_struct_0(X1),X2,X3),X1)
                  & m1_subset_1(k7_domain_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
              <=> ( r3_orders_2(X1,X2,X3)
                  | r3_orders_2(X1,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_orders_2)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

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

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_15,plain,(
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | m1_subset_1(u1_orders_2(X35),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X35)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_16,plain,(
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
      & ( esk1_3(X17,X18,X19) != X17
        | ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( esk1_3(X17,X18,X19) != X18
        | ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k2_tarski(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X19)
        | esk1_3(X17,X18,X19) = X17
        | esk1_3(X17,X18,X19) = X18
        | X19 = k2_tarski(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_17,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( ~ r7_relat_2(X21,X22)
        | ~ r2_hidden(X23,X22)
        | ~ r2_hidden(X24,X22)
        | r2_hidden(k4_tarski(X23,X24),X21)
        | r2_hidden(k4_tarski(X24,X23),X21)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk2_2(X21,X25),X25)
        | r7_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk3_2(X21,X25),X25)
        | r7_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X21,X25),esk3_2(X21,X25)),X21)
        | r7_relat_2(X21,X25)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X21,X25),esk2_2(X21,X25)),X21)
        | r7_relat_2(X21,X25)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ( v6_orders_2(k7_domain_1(u1_struct_0(X1),X2,X3),X1)
                    & m1_subset_1(k7_domain_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
                <=> ( r3_orders_2(X1,X2,X3)
                    | r3_orders_2(X1,X3,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_orders_2])).

cnf(c_0_21,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r3_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) )
    & ( ~ r3_orders_2(esk4_0,esk6_0,esk5_0)
      | ~ v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) )
    & ( v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)
      | r3_orders_2(esk4_0,esk5_0,esk6_0)
      | r3_orders_2(esk4_0,esk6_0,esk5_0) )
    & ( m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
      | r3_orders_2(esk4_0,esk5_0,esk6_0)
      | r3_orders_2(esk4_0,esk6_0,esk5_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])])).

fof(c_0_25,plain,(
    ! [X37,X38,X39] :
      ( v1_xboole_0(X37)
      | ~ m1_subset_1(X38,X37)
      | ~ m1_subset_1(X39,X37)
      | k7_domain_1(X37,X38,X39) = k2_tarski(X38,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

fof(c_0_26,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r1_orders_2(X28,X29,X30)
        | r2_hidden(k4_tarski(X29,X30),u1_orders_2(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) )
      & ( ~ r2_hidden(k4_tarski(X29,X30),u1_orders_2(X28))
        | r1_orders_2(X28,X29,X30)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,u1_struct_0(X28))
        | ~ l1_orders_2(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | X3 != k2_tarski(X2,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_2(u1_orders_2(X1),X2),X2)
    | r7_relat_2(u1_orders_2(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X31,X32,X33] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | ~ m1_subset_1(X33,X31)
      | m1_subset_1(k7_domain_1(X31,X32,X33),k1_zfmisc_1(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

fof(c_0_32,plain,(
    ! [X36] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ v1_xboole_0(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_33,plain,(
    ! [X34] :
      ( ~ l1_orders_2(X34)
      | l1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk3_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_2(u1_orders_2(esk4_0),X1),X1)
    | r7_relat_2(u1_orders_2(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_40,plain,(
    ! [X40,X41,X42] :
      ( ( ~ r3_orders_2(X40,X41,X42)
        | r1_orders_2(X40,X41,X42)
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ m1_subset_1(X42,u1_struct_0(X40)) )
      & ( ~ r1_orders_2(X40,X41,X42)
        | r3_orders_2(X40,X41,X42)
        | v2_struct_0(X40)
        | ~ v3_orders_2(X40)
        | ~ l1_orders_2(X40)
        | ~ m1_subset_1(X41,u1_struct_0(X40))
        | ~ m1_subset_1(X42,u1_struct_0(X40)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r7_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(X3,X4),X1)
    | r2_hidden(k4_tarski(X4,X3),X1)
    | ~ r7_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),X1,esk6_0) = k2_tarski(X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_48,plain,
    ( r7_relat_2(u1_orders_2(X1),X2)
    | ~ r1_orders_2(X1,esk3_2(u1_orders_2(X1),X2),esk2_2(u1_orders_2(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk2_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ m1_subset_1(esk3_2(u1_orders_2(X1),X2),u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(X1,X1)) = X1
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,plain,
    ( r2_hidden(esk3_2(u1_orders_2(X1),X2),X2)
    | r7_relat_2(u1_orders_2(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_23])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X3)
    | ~ r7_relat_2(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_43])).

fof(c_0_56,plain,(
    ! [X10,X11] :
      ( ( ~ v6_orders_2(X11,X10)
        | r7_relat_2(u1_orders_2(X10),X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_orders_2(X10) )
      & ( ~ r7_relat_2(u1_orders_2(X10),X11)
        | v6_orders_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk6_0,esk6_0) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X1))
    | ~ r1_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X1)),X1)
    | ~ m1_subset_1(esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X1)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_29])])).

cnf(c_0_61,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk6_0)
    | ~ r3_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_35]),c_0_51]),c_0_29])]),c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk3_2(u1_orders_2(esk4_0),X1),X1)
    | r7_relat_2(u1_orders_2(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_29])).

cnf(c_0_63,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | ~ r7_relat_2(X2,k2_tarski(X3,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_35])).

cnf(c_0_66,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk6_0,esk6_0) = k2_tarski(esk6_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_29])]),c_0_52])).

cnf(c_0_67,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk6_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(esk6_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(esk3_2(u1_orders_2(esk4_0),k2_tarski(esk6_0,esk6_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_35])])).

cnf(c_0_68,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X1)) = X1
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_70,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X48))
      | m1_subset_1(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_72,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ v6_orders_2(k2_tarski(X3,X1),X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(k2_tarski(X3,X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_23])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_74,plain,
    ( v6_orders_2(X2,X1)
    | ~ r7_relat_2(u1_orders_2(X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_75,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk6_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_35])])).

fof(c_0_76,plain,(
    ! [X43,X44,X45] :
      ( v2_struct_0(X43)
      | ~ v3_orders_2(X43)
      | ~ l1_orders_2(X43)
      | ~ m1_subset_1(X44,u1_struct_0(X43))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | r3_orders_2(X43,X44,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X3) ),
    inference(er,[status(thm)],[c_0_69])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_71])).

cnf(c_0_80,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk6_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_29])])).

cnf(c_0_82,negated_conjecture,
    ( v6_orders_2(k2_tarski(esk6_0,esk6_0),esk4_0)
    | ~ r3_orders_2(esk4_0,esk6_0,esk6_0)
    | ~ m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_29])])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | r2_hidden(k4_tarski(X2,X1),X3)
    | ~ r2_hidden(X2,k2_tarski(X4,X1))
    | ~ r7_relat_2(X3,k2_tarski(X4,X1))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_42,c_0_55])).

cnf(c_0_85,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_87,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_80]),c_0_29])]),c_0_52])).

cnf(c_0_89,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk4_0))
    | ~ r3_orders_2(esk4_0,esk6_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_35]),c_0_51]),c_0_29])]),c_0_52])).

cnf(c_0_91,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | r2_hidden(k4_tarski(X2,X1),X3)
    | ~ r7_relat_2(X3,k2_tarski(X1,X2))
    | ~ v1_relat_1(X3) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r3_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)
    | r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r3_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_94,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) = X1
    | esk2_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) = X2
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_39])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,k2_tarski(esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_96,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_35])])).

cnf(c_0_98,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | r2_hidden(k4_tarski(X2,X1),u1_orders_2(X3))
    | ~ v6_orders_2(k2_tarski(X2,X1),X3)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(k2_tarski(X2,X1),k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_64]),c_0_23])).

cnf(c_0_99,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r3_orders_2(esk4_0,esk6_0,esk5_0)
    | m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_92,c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r3_orders_2(esk4_0,esk6_0,esk5_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_93,c_0_88])).

cnf(c_0_101,plain,
    ( r7_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_102,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) = X1
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X2))
    | ~ r1_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)),X2)
    | ~ m1_subset_1(esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_94]),c_0_29])])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | m1_subset_1(esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_62])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r1_orders_2(esk4_0,esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_29]),c_0_35])])).

cnf(c_0_105,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk4_0))
    | r2_hidden(k4_tarski(esk6_0,esk5_0),u1_orders_2(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_29])]),c_0_100])).

cnf(c_0_106,plain,
    ( r7_relat_2(u1_orders_2(X1),X2)
    | ~ r1_orders_2(X1,esk2_2(u1_orders_2(X1),X2),esk3_2(u1_orders_2(X1),X2))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk3_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ m1_subset_1(esk2_2(u1_orders_2(X1),X2),u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_37]),c_0_23])).

cnf(c_0_107,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r1_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_35])])).

cnf(c_0_108,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) = X1
    | esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) = X2
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_62])).

cnf(c_0_109,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_104]),c_0_29])]),c_0_52])).

cnf(c_0_110,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_111,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r3_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_105]),c_0_29]),c_0_71]),c_0_35])])).

cnf(c_0_112,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),X1,esk5_0) = k2_tarski(X1,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_71])).

cnf(c_0_113,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)) = X1
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(X1,X2))
    | ~ r1_orders_2(esk4_0,X2,esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)))
    | ~ m1_subset_1(esk3_2(u1_orders_2(esk4_0),k2_tarski(X1,X2)),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_94]),c_0_29])])).

cnf(c_0_114,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])])).

cnf(c_0_115,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_71]),c_0_51]),c_0_29])]),c_0_52])).

cnf(c_0_116,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_111]),c_0_29]),c_0_35]),c_0_71])])).

cnf(c_0_117,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),X1,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_71])).

cnf(c_0_118,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_112,c_0_71])).

cnf(c_0_119,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,esk5_0)
    | ~ r3_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_71]),c_0_51]),c_0_29])]),c_0_52])).

cnf(c_0_120,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_71]),c_0_35])])).

cnf(c_0_121,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,esk6_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_35]),c_0_51]),c_0_29])]),c_0_52])).

cnf(c_0_122,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | r3_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_35])])).

cnf(c_0_123,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_61]),c_0_103])).

cnf(c_0_124,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_117,c_0_71])).

cnf(c_0_125,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk5_0) = k2_tarski(esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_118]),c_0_29])]),c_0_52])).

cnf(c_0_126,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0))
    | ~ r3_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0)),esk5_0)
    | ~ m1_subset_1(esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_119]),c_0_71])])).

cnf(c_0_127,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_119]),c_0_35])])).

cnf(c_0_128,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | r3_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_71])])).

cnf(c_0_129,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_123,c_0_114])).

cnf(c_0_130,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_131,negated_conjecture,
    ( r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk5_0))
    | ~ r3_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_126,c_0_68]),c_0_71])])).

cnf(c_0_132,negated_conjecture,
    ( esk2_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_128]),c_0_129])).

cnf(c_0_133,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_130]),c_0_29])])).

cnf(c_0_134,negated_conjecture,
    ( v6_orders_2(k2_tarski(esk5_0,esk5_0),esk4_0)
    | ~ r3_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_131]),c_0_29])])).

cnf(c_0_135,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r1_orders_2(esk4_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_132]),c_0_29]),c_0_71])]),c_0_103])).

cnf(c_0_136,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r1_orders_2(esk4_0,esk5_0,esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_132]),c_0_29]),c_0_71])]),c_0_103])).

cnf(c_0_137,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0))
    | ~ r3_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_130])).

cnf(c_0_138,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_108])).

cnf(c_0_139,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_136,c_0_108])).

cnf(c_0_140,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_90]),c_0_71])])).

cnf(c_0_141,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_119]),c_0_35])])).

cnf(c_0_142,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0))
    | ~ r3_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_61]),c_0_71])])).

cnf(c_0_143,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_140]),c_0_29]),c_0_71])])).

cnf(c_0_144,negated_conjecture,
    ( esk3_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_128]),c_0_142])).

cnf(c_0_145,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_143]),c_0_29])]),c_0_52])).

cnf(c_0_146,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_147,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r7_relat_2(u1_orders_2(esk4_0),k2_tarski(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_144]),c_0_145])])).

cnf(c_0_148,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[c_0_79,c_0_88])).

cnf(c_0_149,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_146,c_0_88]),c_0_88])).

cnf(c_0_150,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_147]),c_0_29])]),c_0_148])).

cnf(c_0_151,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r3_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_150]),c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_153,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_151]),c_0_29])]),c_0_52])).

cnf(c_0_154,negated_conjecture,
    ( ~ r3_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_152,c_0_88]),c_0_88])).

cnf(c_0_155,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_128,c_0_153])).

cnf(c_0_156,negated_conjecture,
    ( ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_154,c_0_155])])).

cnf(c_0_157,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_150]),c_0_148])).

cnf(c_0_158,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_157]),c_0_29])]),c_0_52]),
    [proof]).

%------------------------------------------------------------------------------
