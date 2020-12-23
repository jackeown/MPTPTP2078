%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 (  98 expanded)
%              Number of clauses        :   29 (  35 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  209 ( 467 expanded)
%              Number of equality atoms :   68 (  68 expanded)
%              Maximal formula depth    :   37 (   5 average)
%              Maximal clause size      :   52 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(t49_orders_2,axiom,(
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
             => ~ ( r2_hidden(X2,X3)
                  & r2_hidden(X2,k2_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t35_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)
            & m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(d4_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] :
      ( X7 = k4_enumset1(X1,X2,X3,X4,X5,X6)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X8 != X1
              & X8 != X2
              & X8 != X3
              & X8 != X4
              & X8 != X5
              & X8 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t50_orders_2])).

fof(c_0_14,plain,(
    ! [X50,X51,X52] :
      ( v2_struct_0(X50)
      | ~ v3_orders_2(X50)
      | ~ v4_orders_2(X50)
      | ~ v5_orders_2(X50)
      | ~ l1_orders_2(X50)
      | ~ m1_subset_1(X51,u1_struct_0(X50))
      | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50)))
      | ~ r2_hidden(X51,X52)
      | ~ r2_hidden(X51,k2_orders_2(X50,X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).

fof(c_0_15,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | m1_subset_1(X41,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_16,plain,(
    ! [X48,X49] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X48),X49),X48)
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v3_orders_2(X48)
        | ~ l1_orders_2(X48) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X48),X49),k1_zfmisc_1(u1_struct_0(X48)))
        | ~ m1_subset_1(X49,u1_struct_0(X48))
        | v2_struct_0(X48)
        | ~ v3_orders_2(X48)
        | ~ l1_orders_2(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

fof(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_18,plain,(
    ! [X46,X47] :
      ( v1_xboole_0(X46)
      | ~ m1_subset_1(X47,X46)
      | k6_domain_1(X46,X47) = k1_tarski(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_19,plain,(
    ! [X9] : k2_tarski(X9,X9) = k1_tarski(X9) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11] : k1_enumset1(X10,X10,X11) = k2_tarski(X10,X11) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X12,X13,X14] : k2_enumset1(X12,X12,X13,X14) = k1_enumset1(X12,X13,X14) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X15,X16,X17,X18] : k3_enumset1(X15,X15,X16,X17,X18) = k2_enumset1(X15,X16,X17,X18) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_23,plain,(
    ! [X19,X20,X21,X22,X23] : k4_enumset1(X19,X19,X20,X21,X22,X23) = k3_enumset1(X19,X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k2_orders_2(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k2_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_41,plain,(
    ! [X44] :
      ( v2_struct_0(X44)
      | ~ l1_struct_0(X44)
      | ~ v1_xboole_0(u1_struct_0(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_42,plain,
    ( k6_domain_1(X1,X2) = k4_enumset1(X2,X2,X2,X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

fof(c_0_43,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30,X31,X32,X33,X34,X35,X36,X37,X38,X39] :
      ( ( ~ r2_hidden(X31,X30)
        | X31 = X24
        | X31 = X25
        | X31 = X26
        | X31 = X27
        | X31 = X28
        | X31 = X29
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( X32 != X24
        | r2_hidden(X32,X30)
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( X32 != X25
        | r2_hidden(X32,X30)
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( X32 != X26
        | r2_hidden(X32,X30)
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( X32 != X27
        | r2_hidden(X32,X30)
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( X32 != X28
        | r2_hidden(X32,X30)
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( X32 != X29
        | r2_hidden(X32,X30)
        | X30 != k4_enumset1(X24,X25,X26,X27,X28,X29) )
      & ( esk1_7(X33,X34,X35,X36,X37,X38,X39) != X33
        | ~ r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( esk1_7(X33,X34,X35,X36,X37,X38,X39) != X34
        | ~ r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( esk1_7(X33,X34,X35,X36,X37,X38,X39) != X35
        | ~ r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( esk1_7(X33,X34,X35,X36,X37,X38,X39) != X36
        | ~ r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( esk1_7(X33,X34,X35,X36,X37,X38,X39) != X37
        | ~ r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( esk1_7(X33,X34,X35,X36,X37,X38,X39) != X38
        | ~ r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) )
      & ( r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)
        | esk1_7(X33,X34,X35,X36,X37,X38,X39) = X33
        | esk1_7(X33,X34,X35,X36,X37,X38,X39) = X34
        | esk1_7(X33,X34,X35,X36,X37,X38,X39) = X35
        | esk1_7(X33,X34,X35,X36,X37,X38,X39) = X36
        | esk1_7(X33,X34,X35,X36,X37,X38,X39) = X37
        | esk1_7(X33,X34,X35,X36,X37,X38,X39) = X38
        | X39 = k4_enumset1(X33,X34,X35,X36,X37,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_hidden(X1,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_27])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k4_enumset1(X2,X4,X5,X6,X7,X8) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_30])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).

fof(c_0_52,plain,(
    ! [X45] :
      ( ~ l1_orders_2(X45)
      | l1_struct_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_53,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t50_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_orders_2)).
% 0.13/0.38  fof(t49_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k2_orders_2(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_orders_2)).
% 0.13/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.38  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 0.13/0.38  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.13/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.38  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.13/0.38  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(d4_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:(X7=k4_enumset1(X1,X2,X3,X4,X5,X6)<=>![X8]:(r2_hidden(X8,X7)<=>~((((((X8!=X1&X8!=X2)&X8!=X3)&X8!=X4)&X8!=X5)&X8!=X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 0.13/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), inference(assume_negation,[status(cth)],[t50_orders_2])).
% 0.13/0.38  fof(c_0_14, plain, ![X50, X51, X52]:(v2_struct_0(X50)|~v3_orders_2(X50)|~v4_orders_2(X50)|~v5_orders_2(X50)|~l1_orders_2(X50)|(~m1_subset_1(X51,u1_struct_0(X50))|(~m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X50)))|(~r2_hidden(X51,X52)|~r2_hidden(X51,k2_orders_2(X50,X52)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_orders_2])])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X41, X42, X43]:(~r2_hidden(X41,X42)|~m1_subset_1(X42,k1_zfmisc_1(X43))|m1_subset_1(X41,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.38  fof(c_0_16, plain, ![X48, X49]:((v6_orders_2(k6_domain_1(u1_struct_0(X48),X49),X48)|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v3_orders_2(X48)|~l1_orders_2(X48)))&(m1_subset_1(k6_domain_1(u1_struct_0(X48),X49),k1_zfmisc_1(u1_struct_0(X48)))|~m1_subset_1(X49,u1_struct_0(X48))|(v2_struct_0(X48)|~v3_orders_2(X48)|~l1_orders_2(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.13/0.38  fof(c_0_17, negated_conjecture, (((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.13/0.38  fof(c_0_18, plain, ![X46, X47]:(v1_xboole_0(X46)|~m1_subset_1(X47,X46)|k6_domain_1(X46,X47)=k1_tarski(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.13/0.38  fof(c_0_19, plain, ![X9]:k2_tarski(X9,X9)=k1_tarski(X9), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.38  fof(c_0_20, plain, ![X10, X11]:k1_enumset1(X10,X10,X11)=k2_tarski(X10,X11), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.38  fof(c_0_21, plain, ![X12, X13, X14]:k2_enumset1(X12,X12,X13,X14)=k1_enumset1(X12,X13,X14), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.38  fof(c_0_22, plain, ![X15, X16, X17, X18]:k3_enumset1(X15,X15,X16,X17,X18)=k2_enumset1(X15,X16,X17,X18), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.13/0.38  fof(c_0_23, plain, ![X19, X20, X21, X22, X23]:k4_enumset1(X19,X19,X20,X21,X22,X23)=k3_enumset1(X19,X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.13/0.38  cnf(c_0_24, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,X3)|~r2_hidden(X2,k2_orders_2(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_25, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_26, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_31, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_35, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_36, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_37, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k2_orders_2(X1,X2))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  fof(c_0_41, plain, ![X44]:(v2_struct_0(X44)|~l1_struct_0(X44)|~v1_xboole_0(u1_struct_0(X44))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_42, plain, (k6_domain_1(X1,X2)=k4_enumset1(X2,X2,X2,X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.13/0.38  fof(c_0_43, plain, ![X24, X25, X26, X27, X28, X29, X30, X31, X32, X33, X34, X35, X36, X37, X38, X39]:(((~r2_hidden(X31,X30)|(X31=X24|X31=X25|X31=X26|X31=X27|X31=X28|X31=X29)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29))&((((((X32!=X24|r2_hidden(X32,X30)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29))&(X32!=X25|r2_hidden(X32,X30)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29)))&(X32!=X26|r2_hidden(X32,X30)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29)))&(X32!=X27|r2_hidden(X32,X30)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29)))&(X32!=X28|r2_hidden(X32,X30)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29)))&(X32!=X29|r2_hidden(X32,X30)|X30!=k4_enumset1(X24,X25,X26,X27,X28,X29))))&(((((((esk1_7(X33,X34,X35,X36,X37,X38,X39)!=X33|~r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38))&(esk1_7(X33,X34,X35,X36,X37,X38,X39)!=X34|~r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(esk1_7(X33,X34,X35,X36,X37,X38,X39)!=X35|~r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(esk1_7(X33,X34,X35,X36,X37,X38,X39)!=X36|~r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(esk1_7(X33,X34,X35,X36,X37,X38,X39)!=X37|~r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(esk1_7(X33,X34,X35,X36,X37,X38,X39)!=X38|~r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38)))&(r2_hidden(esk1_7(X33,X34,X35,X36,X37,X38,X39),X39)|(esk1_7(X33,X34,X35,X36,X37,X38,X39)=X33|esk1_7(X33,X34,X35,X36,X37,X38,X39)=X34|esk1_7(X33,X34,X35,X36,X37,X38,X39)=X35|esk1_7(X33,X34,X35,X36,X37,X38,X39)=X36|esk1_7(X33,X34,X35,X36,X37,X38,X39)=X37|esk1_7(X33,X34,X35,X36,X37,X38,X39)=X38)|X39=k4_enumset1(X33,X34,X35,X36,X37,X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_enumset1])])])])])])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (~r2_hidden(X1,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_40]), c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk3_0,k2_orders_2(esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_46, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_42, c_0_27])).
% 0.13/0.38  cnf(c_0_48, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k4_enumset1(X2,X4,X5,X6,X7,X8)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (~r2_hidden(esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k4_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)|~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_30])).
% 0.13/0.38  cnf(c_0_51, plain, (r2_hidden(X1,k4_enumset1(X1,X2,X3,X4,X5,X6))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_48])])).
% 0.13/0.38  fof(c_0_52, plain, ![X45]:(~l1_orders_2(X45)|l1_struct_0(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (~l1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])])).
% 0.13/0.38  cnf(c_0_54, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 29
% 0.13/0.38  # Proof object formula steps           : 27
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 19
% 0.13/0.38  # Proof object initial formulas used   : 13
% 0.13/0.38  # Proof object generating inferences   : 7
% 0.13/0.38  # Proof object simplifying inferences  : 23
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 13
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 33
% 0.13/0.38  # Removed in clause preprocessing      : 5
% 0.13/0.38  # Initial clauses in saturation        : 28
% 0.13/0.38  # Processed clauses                    : 64
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 64
% 0.13/0.38  # Other redundant clauses eliminated   : 13
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 0
% 0.13/0.38  # Generated clauses                    : 22
% 0.13/0.38  # ...of the previous two non-trivial   : 21
% 0.13/0.38  # Contextual simplify-reflections      : 1
% 0.13/0.38  # Paramodulations                      : 15
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 13
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 29
% 0.13/0.38  #    Positive orientable unit clauses  : 14
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 3
% 0.13/0.38  #    Non-unit-clauses                  : 12
% 0.13/0.38  # Current number of unprocessed clauses: 13
% 0.13/0.38  # ...number of literals in the above   : 44
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 33
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 113
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 33
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 14
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 30
% 0.13/0.38  # BW rewrite match successes           : 0
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2601
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
