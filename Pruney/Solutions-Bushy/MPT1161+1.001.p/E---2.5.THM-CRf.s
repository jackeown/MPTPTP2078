%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1161+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:51 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 331 expanded)
%              Number of clauses        :   45 ( 122 expanded)
%              Number of leaves         :   13 (  78 expanded)
%              Depth                    :   15
%              Number of atoms          :  319 (1866 expanded)
%              Number of equality atoms :   45 (  91 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

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

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(irreflexivity_r2_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ~ r2_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

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

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
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

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & r2_hidden(esk6_0,k3_orders_2(esk5_0,esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(X43))
      | k9_subset_1(X43,X44,X45) = k3_xboole_0(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k3_orders_2(X1,X2,X3) = k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)),X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X27,X28] :
      ( v1_xboole_0(X27)
      | ~ m1_subset_1(X28,X27)
      | m1_subset_1(k6_domain_1(X27,X28),k1_zfmisc_1(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_27,plain,(
    ! [X41,X42] :
      ( v1_xboole_0(X41)
      | ~ m1_subset_1(X42,X41)
      | k6_domain_1(X41,X42) = k1_tarski(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_28,plain,(
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

cnf(c_0_29,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),k2_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),X1) = k3_orders_2(esk5_0,X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk5_0),X1,esk7_0) = k3_xboole_0(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_31,plain,(
    ! [X31,X32,X33,X35,X36] :
      ( ( m1_subset_1(esk3_3(X31,X32,X33),u1_struct_0(X32))
        | ~ r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( X31 = esk3_3(X31,X32,X33)
        | ~ r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ r2_hidden(X35,X33)
        | r2_orders_2(X32,esk3_3(X31,X32,X33),X35)
        | ~ r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( m1_subset_1(esk4_4(X31,X32,X33,X36),u1_struct_0(X32))
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( r2_hidden(esk4_4(X31,X32,X33,X36),X33)
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) )
      & ( ~ r2_orders_2(X32,X36,esk4_4(X31,X32,X33,X36))
        | ~ m1_subset_1(X36,u1_struct_0(X32))
        | X31 != X36
        | r2_hidden(X31,a_2_1_orders_2(X32,X33))
        | v2_struct_0(X32)
        | ~ v3_orders_2(X32)
        | ~ v4_orders_2(X32)
        | ~ v5_orders_2(X32)
        | ~ l1_orders_2(X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_32,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X48))
      | m1_subset_1(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk6_0,k3_orders_2(esk5_0,esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( k3_orders_2(esk5_0,esk7_0,esk6_0) = k3_xboole_0(k2_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_30])).

cnf(c_0_38,plain,
    ( r2_orders_2(X2,esk3_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk6_0) = k1_tarski(esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_18])).

fof(c_0_42,plain,(
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

cnf(c_0_43,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_0,k3_xboole_0(k2_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)),esk7_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_37])).

fof(c_0_45,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | k2_orders_2(X6,X7) = a_2_1_orders_2(X6,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_46,plain,
    ( r2_orders_2(X1,esk3_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_0,k2_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( r2_orders_2(esk5_0,esk3_3(X1,esk5_0,k1_tarski(esk6_0)),X2)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_1_orders_2(esk5_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(X2,k1_tarski(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk6_0,k2_orders_2(esk5_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( k2_orders_2(esk5_0,k1_tarski(esk6_0)) = a_2_1_orders_2(esk5_0,k1_tarski(esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_55,plain,
    ( X1 = esk3_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk5_0,esk3_3(X1,esk5_0,k1_tarski(esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_1_orders_2(esk5_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk6_0,a_2_1_orders_2(esk5_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( esk3_3(X1,esk5_0,k1_tarski(esk6_0)) = X1
    | v1_xboole_0(u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,a_2_1_orders_2(esk5_0,k1_tarski(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_47]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_59,plain,(
    ! [X38,X39,X40] :
      ( ~ l1_orders_2(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | ~ r2_orders_2(X38,X39,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).

cnf(c_0_60,negated_conjecture,
    ( r2_orders_2(esk5_0,esk3_3(esk6_0,esk5_0,k1_tarski(esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( esk3_3(esk6_0,esk5_0,k1_tarski(esk6_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_57])).

cnf(c_0_62,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_orders_2(esk5_0,esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

fof(c_0_64,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | ~ v1_xboole_0(u1_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_18]),c_0_19])])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_18])).

fof(c_0_68,plain,(
    ! [X29] :
      ( ~ l1_orders_2(X29)
      | l1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_69,negated_conjecture,
    ( ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_23])).

cnf(c_0_70,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
