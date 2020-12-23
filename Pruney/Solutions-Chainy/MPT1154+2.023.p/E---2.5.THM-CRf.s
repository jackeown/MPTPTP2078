%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:45 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 134 expanded)
%              Number of clauses        :   34 (  50 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  277 ( 702 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   58 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_orders_2,axiom,(
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
                  & r2_hidden(X2,k1_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t48_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ~ r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t38_orders_2,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ ( ? [X4] :
                        ( v6_orders_2(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X2,X4)
                        & r2_hidden(X3,X4) )
                    & ~ r1_orders_2(X1,X2,X3)
                    & ~ r1_orders_2(X1,X3,X2) )
                & ~ ( ( r1_orders_2(X1,X2,X3)
                      | r1_orders_2(X1,X3,X2) )
                    & ! [X4] :
                        ( ( v6_orders_2(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( r2_hidden(X2,X4)
                            & r2_hidden(X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_12,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v3_orders_2(X36)
      | ~ v4_orders_2(X36)
      | ~ v5_orders_2(X36)
      | ~ l1_orders_2(X36)
      | ~ m1_subset_1(X37,u1_struct_0(X36))
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ r2_hidden(X37,X38)
      | ~ r2_hidden(X37,k1_orders_2(X36,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_orders_2])])])])).

fof(c_0_13,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ~ r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t48_orders_2])).

fof(c_0_15,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(X17,X18)
      | m1_subset_1(k1_tarski(X17),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_16,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_17,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_18,plain,(
    ! [X27,X28] :
      ( v1_xboole_0(X27)
      | ~ m1_subset_1(X28,X27)
      | k6_domain_1(X27,X28) = k1_tarski(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_19,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_orders_2(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & r2_hidden(esk4_0,k1_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X19,X20)
      | v1_xboole_0(X20)
      | r2_hidden(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_30,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ v6_orders_2(X34,X31)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r2_hidden(X32,X34)
        | ~ r2_hidden(X33,X34)
        | r1_orders_2(X31,X32,X33)
        | r1_orders_2(X31,X33,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( v6_orders_2(esk2_3(X31,X32,X33),X31)
        | ~ r1_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r1_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( r2_hidden(X32,esk2_3(X31,X32,X33))
        | ~ r1_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( r2_hidden(X33,esk2_3(X31,X32,X33))
        | ~ r1_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( v6_orders_2(esk2_3(X31,X32,X33),X31)
        | ~ r1_orders_2(X31,X33,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ r1_orders_2(X31,X33,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( r2_hidden(X32,esk2_3(X31,X32,X33))
        | ~ r1_orders_2(X31,X33,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) )
      & ( r2_hidden(X33,esk2_3(X31,X32,X33))
        | ~ r1_orders_2(X31,X33,X32)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ v3_orders_2(X31)
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,k1_orders_2(X1,X2))
    | ~ r2_hidden(X3,X2) ),
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk4_0,k1_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_39,plain,
    ( k6_domain_1(X1,X2) = k1_enumset1(X2,X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_24]),c_0_25])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_28,c_0_25])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_45,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v3_orders_2(X29)
      | ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | r1_orders_2(X29,X30,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,X1)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).

cnf(c_0_50,plain,
    ( ~ r1_orders_2(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,esk2_3(X1,X3,X2)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_41])]),c_0_48])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X2,k6_domain_1(X1,X2))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_39])).

cnf(c_0_55,plain,
    ( ~ r1_orders_2(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_41]),c_0_35]),c_0_36])]),c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_41])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_35]),c_0_36]),c_0_57]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 0.19/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.030 s
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t47_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k1_orders_2(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_orders_2)).
% 0.19/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.39  fof(t48_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_orders_2)).
% 0.19/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.39  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.19/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.39  fof(t38_orders_2, axiom, ![X1]:((v3_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(((?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))&~(r1_orders_2(X1,X2,X3)))&~(r1_orders_2(X1,X3,X2))))&~(((r1_orders_2(X1,X2,X3)|r1_orders_2(X1,X3,X2))&![X4]:((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~((r2_hidden(X2,X4)&r2_hidden(X3,X4)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_orders_2)).
% 0.19/0.39  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.19/0.39  fof(c_0_12, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v3_orders_2(X36)|~v4_orders_2(X36)|~v5_orders_2(X36)|~l1_orders_2(X36)|(~m1_subset_1(X37,u1_struct_0(X36))|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|(~r2_hidden(X37,X38)|~r2_hidden(X37,k1_orders_2(X36,X38)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t47_orders_2])])])])).
% 0.19/0.39  fof(c_0_13, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>~(r2_hidden(X2,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), inference(assume_negation,[status(cth)],[t48_orders_2])).
% 0.19/0.39  fof(c_0_15, plain, ![X17, X18]:(~r2_hidden(X17,X18)|m1_subset_1(k1_tarski(X17),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.39  fof(c_0_16, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.39  fof(c_0_17, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.19/0.39  fof(c_0_18, plain, ![X27, X28]:(v1_xboole_0(X27)|~m1_subset_1(X28,X27)|k6_domain_1(X27,X28)=k1_tarski(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.39  fof(c_0_19, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_20, plain, (v2_struct_0(X1)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,X3)|~r2_hidden(X2,k1_orders_2(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.39  cnf(c_0_21, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.39  fof(c_0_22, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&r2_hidden(esk4_0,k1_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.39  cnf(c_0_23, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_26, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_27, plain, ![X19, X20]:(~m1_subset_1(X19,X20)|(v1_xboole_0(X20)|r2_hidden(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.39  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  fof(c_0_29, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.39  fof(c_0_30, plain, ![X31, X32, X33, X34]:((~v6_orders_2(X34,X31)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X31)))|~r2_hidden(X32,X34)|~r2_hidden(X33,X34)|r1_orders_2(X31,X32,X33)|r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31)))&((((v6_orders_2(esk2_3(X31,X32,X33),X31)|~r1_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31)))&(m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))|~r1_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31))))&((r2_hidden(X32,esk2_3(X31,X32,X33))|~r1_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31)))&(r2_hidden(X33,esk2_3(X31,X32,X33))|~r1_orders_2(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31)))))&(((v6_orders_2(esk2_3(X31,X32,X33),X31)|~r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31)))&(m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))|~r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31))))&((r2_hidden(X32,esk2_3(X31,X32,X33))|~r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31)))&(r2_hidden(X33,esk2_3(X31,X32,X33))|~r1_orders_2(X31,X33,X32)|~m1_subset_1(X33,u1_struct_0(X31))|~m1_subset_1(X32,u1_struct_0(X31))|(~v3_orders_2(X31)|~l1_orders_2(X31))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).
% 0.19/0.39  cnf(c_0_31, plain, (v2_struct_0(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~l1_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,k1_orders_2(X1,X2))|~r2_hidden(X3,X2)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk4_0,k1_orders_2(esk3_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_38, plain, (m1_subset_1(k1_enumset1(X1,X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.19/0.39  cnf(c_0_39, plain, (k6_domain_1(X1,X2)=k1_enumset1(X2,X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_24]), c_0_25])).
% 0.19/0.39  cnf(c_0_40, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_42, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_28, c_0_25])).
% 0.19/0.39  cnf(c_0_43, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_44, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  fof(c_0_45, plain, ![X29, X30]:(v2_struct_0(X29)|~v3_orders_2(X29)|~l1_orders_2(X29)|(~m1_subset_1(X30,u1_struct_0(X29))|r1_orders_2(X29,X30,X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (~m1_subset_1(k6_domain_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r2_hidden(esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_47, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X2,X1)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|r2_hidden(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_49, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_42])])).
% 0.19/0.39  cnf(c_0_50, plain, (~r1_orders_2(X1,X2,X3)|~l1_orders_2(X1)|~v3_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X4,esk2_3(X1,X3,X2))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.39  cnf(c_0_51, plain, (r2_hidden(X1,esk2_3(X2,X3,X1))|~r1_orders_2(X2,X1,X3)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_52, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|~r2_hidden(esk4_0,k6_domain_1(u1_struct_0(esk3_0),esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_41])]), c_0_48])).
% 0.19/0.39  cnf(c_0_54, plain, (v1_xboole_0(X1)|r2_hidden(X2,k6_domain_1(X1,X2))|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_49, c_0_39])).
% 0.19/0.39  cnf(c_0_55, plain, (~r1_orders_2(X1,X2,X3)|~l1_orders_2(X1)|~v3_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_41]), c_0_35]), c_0_36])]), c_0_37])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_41])])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_35]), c_0_36]), c_0_57]), c_0_41])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 59
% 0.19/0.39  # Proof object clause steps            : 34
% 0.19/0.39  # Proof object formula steps           : 25
% 0.19/0.39  # Proof object conjectures             : 16
% 0.19/0.39  # Proof object clause conjectures      : 13
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 19
% 0.19/0.39  # Proof object initial formulas used   : 12
% 0.19/0.39  # Proof object generating inferences   : 10
% 0.19/0.39  # Proof object simplifying inferences  : 28
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 12
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 31
% 0.19/0.39  # Removed in clause preprocessing      : 2
% 0.19/0.39  # Initial clauses in saturation        : 29
% 0.19/0.39  # Processed clauses                    : 101
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 37
% 0.19/0.39  # ...remaining for further processing  : 64
% 0.19/0.39  # Other redundant clauses eliminated   : 5
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 3
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 112
% 0.19/0.39  # ...of the previous two non-trivial   : 88
% 0.19/0.39  # Contextual simplify-reflections      : 2
% 0.19/0.39  # Paramodulations                      : 109
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 5
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 57
% 0.19/0.39  #    Positive orientable unit clauses  : 13
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 3
% 0.19/0.39  #    Non-unit-clauses                  : 41
% 0.19/0.39  # Current number of unprocessed clauses: 15
% 0.19/0.39  # ...number of literals in the above   : 102
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 6
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1377
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 167
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 39
% 0.19/0.39  # Unit Clause-clause subsumption calls : 17
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 3
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 4495
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.035 s
% 0.19/0.39  # System time              : 0.004 s
% 0.19/0.39  # Total time               : 0.040 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
