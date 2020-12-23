%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1161+1.002 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 663 expanded)
%              Number of clauses        :   54 ( 244 expanded)
%              Number of leaves         :   16 ( 160 expanded)
%              Depth                    :   15
%              Number of atoms          :  363 (3439 expanded)
%              Number of equality atoms :   50 ( 120 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ r2_hidden(X2,k3_orders_2(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(dt_k3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_orders_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(fraenkel_a_2_1_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(irreflexivity_r2_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ~ r2_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ r2_hidden(X2,k3_orders_2(X1,X3,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_orders_2])).

fof(c_0_17,plain,(
    ! [X49,X50] :
      ( ~ m1_subset_1(X49,X50)
      | v1_xboole_0(X50)
      | r2_hidden(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_18,plain,(
    ! [X32] : m1_subset_1(esk3_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ v3_orders_2(X27)
      | ~ v4_orders_2(X27)
      | ~ v5_orders_2(X27)
      | ~ l1_orders_2(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | m1_subset_1(k3_orders_2(X27,X28,X29),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_orders_2])])])).

fof(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v3_orders_2(esk6_0)
    & v4_orders_2(esk6_0)
    & v5_orders_2(esk6_0)
    & l1_orders_2(esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & r2_hidden(esk7_0,k3_orders_2(esk6_0,esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_21,plain,(
    ! [X30,X31] :
      ( v1_xboole_0(X30)
      | ~ m1_subset_1(X31,X30)
      | m1_subset_1(k6_domain_1(X30,X31),k1_zfmisc_1(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_22,plain,(
    ! [X44,X45] :
      ( v1_xboole_0(X44)
      | ~ m1_subset_1(X45,X44)
      | k6_domain_1(X44,X45) = k1_tarski(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_23,plain,(
    ! [X54,X55,X56] :
      ( ~ r2_hidden(X54,X55)
      | ~ m1_subset_1(X55,k1_zfmisc_1(X56))
      | ~ v1_xboole_0(X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_orders_2(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( l1_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v5_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( v4_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v3_orders_2(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_33,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ v1_xboole_0(X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk3_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk6_0,X1,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk7_0,k3_orders_2(esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_42,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | k2_orders_2(X6,X7) = a_2_1_orders_2(X6,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_43,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk6_0),esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k1_tarski(esk7_0)
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k3_orders_2(esk6_0,esk8_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(k3_orders_2(esk6_0,esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | m1_subset_1(k1_tarski(esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,plain,(
    ! [X8,X9,X10] :
      ( v2_struct_0(X8)
      | ~ v3_orders_2(X8)
      | ~ v4_orders_2(X8)
      | ~ v5_orders_2(X8)
      | ~ l1_orders_2(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | k3_orders_2(X8,X9,X10) = k9_subset_1(u1_struct_0(X8),k2_orders_2(X8,k6_domain_1(u1_struct_0(X8),X10)),X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d14_orders_2])])])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k2_orders_2(esk6_0,k1_tarski(esk7_0)) = a_2_1_orders_2(esk6_0,k1_tarski(esk7_0))
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

fof(c_0_53,plain,(
    ! [X46,X47,X48] :
      ( ~ m1_subset_1(X48,k1_zfmisc_1(X46))
      | k9_subset_1(X46,X47,X48) = k3_xboole_0(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk7_0) = k1_tarski(esk7_0) ),
    inference(sr,[status(thm)],[c_0_44,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( k2_orders_2(esk6_0,k1_tarski(esk7_0)) = a_2_1_orders_2(esk6_0,k1_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_57,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_58,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r2_hidden(X21,X18)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(X22,X18)
        | ~ r2_hidden(X22,X19)
        | r2_hidden(X22,X20)
        | X20 != k3_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X23,X24,X25),X25)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X23)
        | ~ r2_hidden(esk2_3(X23,X24,X25),X24)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X23)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) )
      & ( r2_hidden(esk2_3(X23,X24,X25),X24)
        | r2_hidden(esk2_3(X23,X24,X25),X25)
        | X25 = k3_xboole_0(X23,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_59,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),a_2_1_orders_2(esk6_0,k1_tarski(esk7_0)),X1) = k3_orders_2(esk6_0,X1,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_27]),c_0_55]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),X1,esk8_0) = k3_xboole_0(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

fof(c_0_61,plain,(
    ! [X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X13,X12)
        | X13 = X11
        | X12 != k1_tarski(X11) )
      & ( X14 != X11
        | r2_hidden(X14,X12)
        | X12 != k1_tarski(X11) )
      & ( ~ r2_hidden(esk1_2(X15,X16),X16)
        | esk1_2(X15,X16) != X15
        | X16 = k1_tarski(X15) )
      & ( r2_hidden(esk1_2(X15,X16),X16)
        | esk1_2(X15,X16) = X15
        | X16 = k1_tarski(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_62,plain,(
    ! [X34,X35,X36,X38,X39] :
      ( ( m1_subset_1(esk4_3(X34,X35,X36),u1_struct_0(X35))
        | ~ r2_hidden(X34,a_2_1_orders_2(X35,X36))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( X34 = esk4_3(X34,X35,X36)
        | ~ r2_hidden(X34,a_2_1_orders_2(X35,X36))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( ~ m1_subset_1(X38,u1_struct_0(X35))
        | ~ r2_hidden(X38,X36)
        | r2_orders_2(X35,esk4_3(X34,X35,X36),X38)
        | ~ r2_hidden(X34,a_2_1_orders_2(X35,X36))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( m1_subset_1(esk5_4(X34,X35,X36,X39),u1_struct_0(X35))
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | X34 != X39
        | r2_hidden(X34,a_2_1_orders_2(X35,X36))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( r2_hidden(esk5_4(X34,X35,X36,X39),X36)
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | X34 != X39
        | r2_hidden(X34,a_2_1_orders_2(X35,X36))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) )
      & ( ~ r2_orders_2(X35,X39,esk5_4(X34,X35,X36,X39))
        | ~ m1_subset_1(X39,u1_struct_0(X35))
        | X34 != X39
        | r2_hidden(X34,a_2_1_orders_2(X35,X36))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ v4_orders_2(X35)
        | ~ v5_orders_2(X35)
        | ~ l1_orders_2(X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_63,plain,(
    ! [X51,X52,X53] :
      ( ~ r2_hidden(X51,X52)
      | ~ m1_subset_1(X52,k1_zfmisc_1(X53))
      | m1_subset_1(X51,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,negated_conjecture,
    ( k3_orders_2(esk6_0,esk8_0,esk7_0) = k3_xboole_0(a_2_1_orders_2(esk6_0,k1_tarski(esk7_0)),esk8_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_39]),c_0_60])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,plain,
    ( r2_orders_2(X2,esk4_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk7_0,k3_xboole_0(a_2_1_orders_2(esk6_0,k1_tarski(esk7_0)),esk8_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_65])).

cnf(c_0_71,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_66])])).

cnf(c_0_73,plain,
    ( r2_orders_2(X1,esk4_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk7_0,a_2_1_orders_2(esk6_0,k1_tarski(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[c_0_49,c_0_51])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_72])).

fof(c_0_79,plain,(
    ! [X41,X42,X43] :
      ( ~ l1_orders_2(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | ~ r2_orders_2(X41,X42,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).

cnf(c_0_80,plain,
    ( r2_orders_2(X1,esk4_3(X2,X1,X3),esk3_1(X3))
    | v1_xboole_0(X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_37])).

cnf(c_0_81,negated_conjecture,
    ( esk4_3(esk7_0,esk6_0,k1_tarski(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_82,plain,
    ( esk3_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_37]),c_0_78])).

cnf(c_0_83,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( r2_orders_2(esk6_0,esk7_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_75]),c_0_81]),c_0_82]),c_0_76]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_78]),c_0_32])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_27]),c_0_28])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_85]),
    [proof]).

%------------------------------------------------------------------------------
