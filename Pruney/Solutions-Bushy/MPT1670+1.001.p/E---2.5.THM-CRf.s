%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1670+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:34 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  136 (9838 expanded)
%              Number of clauses        :  103 (4019 expanded)
%              Number of leaves         :   16 (2434 expanded)
%              Depth                    :   32
%              Number of atoms          :  476 (41022 expanded)
%              Number of equality atoms :   26 (1169 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_tarski(X2,k11_waybel_0(X1,X2))
            & r1_tarski(X2,k12_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_waybel_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(fraenkel_a_2_2_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_2_waybel_0(X2,X3))
      <=> ? [X4] :
            ( v1_finset_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(X3))
            & X1 = k1_yellow_0(X2,X4)
            & r1_yellow_0(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_waybel_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(fc1_finset_1,axiom,(
    ! [X1] : v1_finset_1(k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

fof(t39_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
            & k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d27_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k11_waybel_0(X1,X2) = a_2_2_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d27_waybel_0)).

fof(t38_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
            & r2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_0)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(d28_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k12_waybel_0(X1,X2) = a_2_3_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d28_waybel_0)).

fof(fraenkel_a_2_3_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_3_waybel_0(X2,X3))
      <=> ? [X4] :
            ( v1_finset_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(X3))
            & X1 = k2_yellow_0(X2,X4)
            & r2_yellow_0(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_3_waybel_0)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r1_tarski(X2,k11_waybel_0(X1,X2))
              & r1_tarski(X2,k12_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_waybel_0])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ r1_tarski(esk5_0,k11_waybel_0(esk4_0,esk5_0))
      | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_18,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk1_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k11_waybel_0(esk4_0,esk5_0))
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X32,X33] :
      ( ( ~ r1_tarski(k1_tarski(X32),X33)
        | r2_hidden(X32,X33) )
      & ( ~ r2_hidden(X32,X33)
        | r1_tarski(k1_tarski(X32),X33) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( ~ r2_hidden(X44,X45)
      | ~ v1_xboole_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_tarski(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

fof(c_0_28,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_29,plain,(
    ! [X28,X29] :
      ( v1_xboole_0(X28)
      | ~ m1_subset_1(X29,X28)
      | k6_domain_1(X28,X29) = k1_tarski(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(esk1_2(k1_tarski(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_2(k1_tarski(X1),X2),k1_tarski(X1))
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_26])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(k6_domain_1(esk5_0,X1),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_37,plain,
    ( k6_domain_1(X1,X2) = k6_domain_1(X3,X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X2,X3) ),
    inference(spm,[status(thm)],[c_0_34,c_0_34])).

fof(c_0_38,plain,(
    ! [X18,X19,X20,X22] :
      ( ( v1_finset_1(esk2_3(X18,X19,X20))
        | ~ r2_hidden(X18,a_2_2_waybel_0(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( m1_subset_1(esk2_3(X18,X19,X20),k1_zfmisc_1(X20))
        | ~ r2_hidden(X18,a_2_2_waybel_0(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( X18 = k1_yellow_0(X19,esk2_3(X18,X19,X20))
        | ~ r2_hidden(X18,a_2_2_waybel_0(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( r1_yellow_0(X19,esk2_3(X18,X19,X20))
        | ~ r2_hidden(X18,a_2_2_waybel_0(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) )
      & ( ~ v1_finset_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(X20))
        | X18 != k1_yellow_0(X19,X22)
        | ~ r1_yellow_0(X19,X22)
        | r2_hidden(X18,a_2_2_waybel_0(X19,X20))
        | v2_struct_0(X19)
        | ~ l1_orders_2(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_2_waybel_0])])])])])])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(X2,esk5_0)
    | ~ m1_subset_1(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32])).

fof(c_0_41,plain,(
    ! [X30,X31] :
      ( ~ r2_hidden(X30,X31)
      | m1_subset_1(X30,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,a_2_2_waybel_0(X4,X2))
    | v2_struct_0(X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | X3 != k1_yellow_0(X4,X1)
    | ~ r1_yellow_0(X4,X1)
    | ~ l1_orders_2(X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k1_tarski(X1),X2),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(X2,k1_tarski(X1))
    | ~ m1_subset_1(X2,esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),a_2_2_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r1_yellow_0(X1,X2)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(X1,k1_tarski(X2))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_34]),c_0_39])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_35])).

fof(c_0_51,plain,(
    ! [X17] : v1_finset_1(k1_tarski(X17)) ),
    inference(variable_rename,[status(thm)],[fc1_finset_1])).

fof(c_0_52,plain,(
    ! [X36,X37] :
      ( ( k1_yellow_0(X36,k6_domain_1(u1_struct_0(X36),X37)) = X37
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36) )
      & ( k2_yellow_0(X36,k6_domain_1(u1_struct_0(X36),X37)) = X37
        | ~ m1_subset_1(X37,u1_struct_0(X36))
        | v2_struct_0(X36)
        | ~ v3_orders_2(X36)
        | ~ v5_orders_2(X36)
        | ~ l1_orders_2(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_yellow_0])])])])])).

fof(c_0_53,plain,(
    ! [X38,X39,X40] :
      ( ~ r2_hidden(X38,X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(X40))
      | m1_subset_1(X38,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_54,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | k11_waybel_0(X5,X6) = a_2_2_waybel_0(X5,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d27_waybel_0])])])])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk4_0,X1),a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r1_yellow_0(esk4_0,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(esk5_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,plain,
    ( v1_finset_1(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_58,plain,
    ( k1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_59,plain,(
    ! [X34,X35] :
      ( ( r1_yellow_0(X34,k6_domain_1(u1_struct_0(X34),X35))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) )
      & ( r2_yellow_0(X34,k6_domain_1(u1_struct_0(X34),X35))
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ v5_orders_2(X34)
        | ~ l1_orders_2(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_yellow_0])])])])])).

cnf(c_0_60,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | k11_waybel_0(X1,X2) = a_2_2_waybel_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_62,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | ~ v1_xboole_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk4_0,k1_tarski(X1)),a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r1_yellow_0(esk4_0,k1_tarski(X1))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_64,plain,
    ( k1_yellow_0(X1,k1_tarski(X2)) = X2
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_34])).

cnf(c_0_65,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_67,plain,
    ( r1_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_46])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_61]),c_0_46]),c_0_47])]),c_0_48])).

fof(c_0_70,plain,(
    ! [X7,X8] :
      ( v2_struct_0(X7)
      | ~ l1_orders_2(X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | k12_waybel_0(X7,X8) = a_2_3_waybel_0(X7,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d28_waybel_0])])])])).

cnf(c_0_71,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(X1,a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r1_yellow_0(esk4_0,k1_tarski(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),c_0_47])]),c_0_48])).

cnf(c_0_73,plain,
    ( r1_yellow_0(X1,k1_tarski(X2))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_27])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_20])).

cnf(c_0_76,plain,
    ( v2_struct_0(X1)
    | k12_waybel_0(X1,X2) = a_2_3_waybel_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_46])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(X1,a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_65]),c_0_66]),c_0_47])]),c_0_48])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r1_tarski(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

fof(c_0_82,plain,(
    ! [X23,X24,X25,X27] :
      ( ( v1_finset_1(esk3_3(X23,X24,X25))
        | ~ r2_hidden(X23,a_2_3_waybel_0(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( m1_subset_1(esk3_3(X23,X24,X25),k1_zfmisc_1(X25))
        | ~ r2_hidden(X23,a_2_3_waybel_0(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( X23 = k2_yellow_0(X24,esk3_3(X23,X24,X25))
        | ~ r2_hidden(X23,a_2_3_waybel_0(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( r2_yellow_0(X24,esk3_3(X23,X24,X25))
        | ~ r2_hidden(X23,a_2_3_waybel_0(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) )
      & ( ~ v1_finset_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X25))
        | X23 != k2_yellow_0(X24,X27)
        | ~ r2_yellow_0(X24,X27)
        | r2_hidden(X23,a_2_3_waybel_0(X24,X25))
        | v2_struct_0(X24)
        | ~ l1_orders_2(X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_3_waybel_0])])])])])])).

cnf(c_0_83,negated_conjecture,
    ( r2_hidden(X1,a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r2_hidden(X2,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_86,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_20])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_88,plain,
    ( r2_hidden(X3,a_2_3_waybel_0(X4,X2))
    | v2_struct_0(X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | X3 != k2_yellow_0(X4,X1)
    | ~ r2_yellow_0(X4,X1)
    | ~ l1_orders_2(X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_87])).

cnf(c_0_93,plain,
    ( r2_hidden(k2_yellow_0(X1,X2),a_2_3_waybel_0(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),k11_waybel_0(esk4_0,esk5_0))
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_91]),c_0_92])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_61]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk4_0,X1),a_2_3_waybel_0(esk4_0,esk5_0))
    | ~ r2_yellow_0(esk4_0,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_99,plain,
    ( k2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_100,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_61]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_61]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk4_0,k1_tarski(X1)),a_2_3_waybel_0(esk4_0,esk5_0))
    | ~ r2_yellow_0(esk4_0,k1_tarski(X1))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_56]),c_0_57])])).

cnf(c_0_104,plain,
    ( k2_yellow_0(X1,k1_tarski(X2)) = X2
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_34])).

cnf(c_0_105,plain,
    ( r2_yellow_0(X1,k6_domain_1(u1_struct_0(X1),X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_61]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_108,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(X1,a_2_3_waybel_0(esk4_0,esk5_0))
    | ~ r2_yellow_0(esk4_0,k1_tarski(X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_65]),c_0_66]),c_0_47])]),c_0_48])).

cnf(c_0_109,plain,
    ( r2_yellow_0(X1,k1_tarski(X2))
    | v1_xboole_0(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_34])).

cnf(c_0_110,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_20])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_107])).

cnf(c_0_112,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(X1,a_2_3_waybel_0(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_65]),c_0_66]),c_0_47])]),c_0_48])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0))
    | m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_20]),c_0_44])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(X1,a_2_3_waybel_0(esk4_0,esk5_0))
    | ~ r2_hidden(X2,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0)
    | r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_119,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r2_hidden(esk1_2(esk5_0,k12_waybel_0(esk4_0,esk5_0)),k12_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_25])).

cnf(c_0_120,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),a_2_3_waybel_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_117])])).

cnf(c_0_121,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),esk5_0)
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_118])).

cnf(c_0_123,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0)
    | ~ r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),a_2_3_waybel_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),a_2_3_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),a_2_3_waybel_0(esk4_0,esk5_0))
    | m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_122])).

cnf(c_0_126,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_68])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_125]),c_0_44])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_126]),c_0_127])])).

cnf(c_0_129,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k11_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_27]),c_0_128])).

cnf(c_0_130,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_2_waybel_0(esk4_0,esk5_0)),a_2_2_waybel_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_61]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_131,negated_conjecture,
    ( ~ r1_tarski(esk5_0,k12_waybel_0(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_130])])).

cnf(c_0_132,negated_conjecture,
    ( ~ r1_tarski(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_76]),c_0_46]),c_0_47])]),c_0_48])).

cnf(c_0_133,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_132,c_0_20])).

cnf(c_0_134,negated_conjecture,
    ( ~ r2_hidden(esk1_2(esk5_0,a_2_3_waybel_0(esk4_0,esk5_0)),a_2_3_waybel_0(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_132,c_0_25])).

cnf(c_0_135,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_133]),c_0_134]),
    [proof]).

%------------------------------------------------------------------------------
