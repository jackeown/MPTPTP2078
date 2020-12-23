%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:52 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   84 (4243 expanded)
%              Number of clauses        :   63 (1445 expanded)
%              Number of leaves         :   10 (1019 expanded)
%              Depth                    :   19
%              Number of atoms          :  377 (30481 expanded)
%              Number of equality atoms :   48 ( 934 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_orders_2,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k2_orders_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(c_0_10,negated_conjecture,(
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
               => ( r2_orders_2(X1,X2,X3)
                <=> r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_orders_2])).

fof(c_0_11,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_12,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X26,X27,X28,X30,X31] :
      ( ( m1_subset_1(esk2_3(X26,X27,X28),u1_struct_0(X27))
        | ~ r2_hidden(X26,a_2_1_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( X26 = esk2_3(X26,X27,X28)
        | ~ r2_hidden(X26,a_2_1_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X30,X28)
        | r2_orders_2(X27,esk2_3(X26,X27,X28),X30)
        | ~ r2_hidden(X26,a_2_1_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( m1_subset_1(esk3_4(X26,X27,X28,X31),u1_struct_0(X27))
        | ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | r2_hidden(X26,a_2_1_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( r2_hidden(esk3_4(X26,X27,X28,X31),X28)
        | ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | r2_hidden(X26,a_2_1_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( ~ r2_orders_2(X27,X31,esk3_4(X26,X27,X28,X31))
        | ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | r2_hidden(X26,a_2_1_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_14,plain,(
    ! [X35,X36] :
      ( ( v6_orders_2(k6_domain_1(u1_struct_0(X35),X36),X35)
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ l1_orders_2(X35) )
      & ( m1_subset_1(k6_domain_1(u1_struct_0(X35),X36),k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | v2_struct_0(X35)
        | ~ v3_orders_2(X35)
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) )
    & ( r2_orders_2(esk4_0,esk5_0,esk6_0)
      | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_25,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk6_0) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_32,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_35,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v3_orders_2(X22)
      | ~ v4_orders_2(X22)
      | ~ v5_orders_2(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k2_orders_2(X22,X23) = a_2_1_orders_2(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

fof(c_0_36,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,a_2_1_orders_2(X1,X4))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | X3 != X2
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0),k2_tarski(esk6_0,esk6_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_46,negated_conjecture,
    ( k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_48,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))
    | ~ r2_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_21]),c_0_28]),c_0_29]),c_0_22]),c_0_27])]),c_0_23]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_30])).

fof(c_0_52,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v3_orders_2(X24)
      | ~ v4_orders_2(X24)
      | ~ v5_orders_2(X24)
      | ~ l1_orders_2(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | m1_subset_1(k2_orders_2(X24,X25),k1_zfmisc_1(u1_struct_0(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).

cnf(c_0_53,plain,
    ( r2_orders_2(X2,esk2_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( r2_orders_2(X1,esk2_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_46]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_63,plain,
    ( r2_orders_2(X1,esk2_3(X2,X1,k2_tarski(X3,X4)),X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k2_tarski(X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,k2_tarski(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_65,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)),esk6_0)
    | ~ m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)) = esk5_0
    | ~ m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_64]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_27]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_34])).

cnf(c_0_71,negated_conjecture,
    ( esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_34])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(rw,[status(thm)],[c_0_69,c_0_46])).

cnf(c_0_74,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_31]),c_0_64])])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78])])).

cnf(c_0_80,negated_conjecture,
    ( k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_68]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_68]),c_0_80]),c_0_21]),c_0_28]),c_0_29]),c_0_22])]),c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_78])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:28:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.17/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.17/0.39  #
% 0.17/0.39  # Preprocessing time       : 0.019 s
% 0.17/0.39  # Presaturation interreduction done
% 0.17/0.39  
% 0.17/0.39  # Proof found!
% 0.17/0.39  # SZS status Theorem
% 0.17/0.39  # SZS output start CNFRefutation
% 0.17/0.39  fof(t52_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_orders_2)).
% 0.17/0.39  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.17/0.39  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.17/0.39  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.17/0.39  fof(t35_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(v6_orders_2(k6_domain_1(u1_struct_0(X1),X2),X1)&m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_orders_2)).
% 0.17/0.39  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.17/0.39  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 0.17/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.17/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.17/0.39  fof(dt_k2_orders_2, axiom, ![X1, X2]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 0.17/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X2,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X3)))))))), inference(assume_negation,[status(cth)],[t52_orders_2])).
% 0.17/0.39  fof(c_0_11, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.17/0.39  fof(c_0_12, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.17/0.39  fof(c_0_13, plain, ![X26, X27, X28, X30, X31]:((((m1_subset_1(esk2_3(X26,X27,X28),u1_struct_0(X27))|~r2_hidden(X26,a_2_1_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&(X26=esk2_3(X26,X27,X28)|~r2_hidden(X26,a_2_1_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))))))&(~m1_subset_1(X30,u1_struct_0(X27))|(~r2_hidden(X30,X28)|r2_orders_2(X27,esk2_3(X26,X27,X28),X30))|~r2_hidden(X26,a_2_1_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))))))&((m1_subset_1(esk3_4(X26,X27,X28,X31),u1_struct_0(X27))|(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31)|r2_hidden(X26,a_2_1_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&((r2_hidden(esk3_4(X26,X27,X28,X31),X28)|(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31)|r2_hidden(X26,a_2_1_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&(~r2_orders_2(X27,X31,esk3_4(X26,X27,X28,X31))|(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31)|r2_hidden(X26,a_2_1_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.17/0.39  fof(c_0_14, plain, ![X35, X36]:((v6_orders_2(k6_domain_1(u1_struct_0(X35),X36),X35)|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v3_orders_2(X35)|~l1_orders_2(X35)))&(m1_subset_1(k6_domain_1(u1_struct_0(X35),X36),k1_zfmisc_1(u1_struct_0(X35)))|~m1_subset_1(X36,u1_struct_0(X35))|(v2_struct_0(X35)|~v3_orders_2(X35)|~l1_orders_2(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t35_orders_2])])])])])).
% 0.17/0.39  fof(c_0_15, negated_conjecture, (((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&((~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))))&(r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.17/0.39  cnf(c_0_16, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.17/0.39  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.39  cnf(c_0_18, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_1_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.39  cnf(c_0_19, plain, (m1_subset_1(k6_domain_1(u1_struct_0(X1),X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_22, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_24, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.17/0.39  fof(c_0_25, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.17/0.39  cnf(c_0_26, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_18])).
% 0.17/0.39  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_28, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_29, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_31, negated_conjecture, (k6_domain_1(u1_struct_0(esk4_0),esk6_0)=k2_tarski(esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_24, c_0_20])).
% 0.17/0.39  cnf(c_0_32, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_34, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.17/0.39  fof(c_0_35, plain, ![X22, X23]:(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k2_orders_2(X22,X23)=a_2_1_orders_2(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.17/0.39  fof(c_0_36, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.17/0.39  cnf(c_0_37, plain, (r2_hidden(X3,a_2_1_orders_2(X1,X4))|v2_struct_0(X1)|~r2_orders_2(X1,X2,esk3_4(X3,X1,X4,X2))|~m1_subset_1(X2,u1_struct_0(X1))|X3!=X2|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.39  cnf(c_0_38, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_32])).
% 0.17/0.39  cnf(c_0_39, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0),k2_tarski(esk6_0,esk6_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.17/0.39  cnf(c_0_40, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.17/0.39  cnf(c_0_41, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.17/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk6_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.17/0.39  cnf(c_0_43, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_orders_2(X1,X2,esk3_4(X2,X1,X3,X2))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_37])).
% 0.17/0.39  cnf(c_0_44, negated_conjecture, (esk3_4(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0),esk5_0)=esk6_0|v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.17/0.39  cnf(c_0_45, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_46, negated_conjecture, (k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))=a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|~v1_xboole_0(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.17/0.39  fof(c_0_48, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.17/0.39  cnf(c_0_49, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))|~r2_orders_2(esk4_0,esk5_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_21]), c_0_28]), c_0_29]), c_0_22]), c_0_27])]), c_0_23]), c_0_34])).
% 0.17/0.39  cnf(c_0_50, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.17/0.39  cnf(c_0_51, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_30])).
% 0.17/0.39  fof(c_0_52, plain, ![X24, X25]:(v2_struct_0(X24)|~v3_orders_2(X24)|~v4_orders_2(X24)|~v5_orders_2(X24)|~l1_orders_2(X24)|~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|m1_subset_1(k2_orders_2(X24,X25),k1_zfmisc_1(u1_struct_0(X24)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k2_orders_2])])])).
% 0.17/0.39  cnf(c_0_53, plain, (r2_orders_2(X2,esk2_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.39  cnf(c_0_54, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.17/0.39  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.39  cnf(c_0_56, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.17/0.39  cnf(c_0_57, plain, (v2_struct_0(X1)|m1_subset_1(k2_orders_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.17/0.39  cnf(c_0_58, plain, (r2_orders_2(X1,esk2_3(X2,X1,X3),X4)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_53, c_0_54])).
% 0.17/0.39  cnf(c_0_59, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_55])])).
% 0.17/0.39  cnf(c_0_60, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))|~v1_xboole_0(X1)|~m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_56])).
% 0.17/0.39  cnf(c_0_61, negated_conjecture, (m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_46]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_62, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_56, c_0_31])).
% 0.17/0.39  cnf(c_0_63, plain, (r2_orders_2(X1,esk2_3(X2,X1,k2_tarski(X3,X4)),X4)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k2_tarski(X3,X4),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,k2_tarski(X3,X4)))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.17/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k2_tarski(esk6_0,esk6_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.17/0.39  cnf(c_0_65, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.39  cnf(c_0_66, negated_conjecture, (r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)),esk6_0)|~m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_67, negated_conjecture, (esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0))=esk5_0|~m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_64]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_27]), c_0_21]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_69, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.17/0.39  cnf(c_0_70, negated_conjecture, (r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0)),esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_34])).
% 0.17/0.39  cnf(c_0_71, negated_conjecture, (esk2_3(esk5_0,esk4_0,k2_tarski(esk6_0,esk6_0))=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_34])).
% 0.17/0.39  cnf(c_0_72, negated_conjecture, (r2_hidden(esk3_4(esk5_0,esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0),esk5_0),k6_domain_1(u1_struct_0(esk4_0),esk5_0))|r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(spm,[status(thm)],[c_0_33, c_0_68])).
% 0.17/0.39  cnf(c_0_73, negated_conjecture, (~r2_orders_2(esk4_0,esk5_0,esk6_0)|~r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(rw,[status(thm)],[c_0_69, c_0_46])).
% 0.17/0.39  cnf(c_0_74, negated_conjecture, (r2_orders_2(esk4_0,esk5_0,esk6_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.17/0.39  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v1_xboole_0(X1)|~m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_72])).
% 0.17/0.39  cnf(c_0_76, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|~r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.17/0.39  cnf(c_0_77, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_75, c_0_68])).
% 0.17/0.39  cnf(c_0_78, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_31]), c_0_64])])).
% 0.17/0.39  cnf(c_0_79, negated_conjecture, (r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78])])).
% 0.17/0.39  cnf(c_0_80, negated_conjecture, (k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))=a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_68]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_81, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_79])).
% 0.17/0.39  cnf(c_0_82, negated_conjecture, (m1_subset_1(a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_68]), c_0_80]), c_0_21]), c_0_28]), c_0_29]), c_0_22])]), c_0_23])).
% 0.17/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_78])]), ['proof']).
% 0.17/0.39  # SZS output end CNFRefutation
% 0.17/0.39  # Proof object total steps             : 84
% 0.17/0.39  # Proof object clause steps            : 63
% 0.17/0.39  # Proof object formula steps           : 21
% 0.17/0.39  # Proof object conjectures             : 46
% 0.17/0.39  # Proof object clause conjectures      : 43
% 0.17/0.39  # Proof object formula conjectures     : 3
% 0.17/0.39  # Proof object initial clauses used    : 22
% 0.17/0.39  # Proof object initial formulas used   : 10
% 0.17/0.39  # Proof object generating inferences   : 32
% 0.17/0.39  # Proof object simplifying inferences  : 77
% 0.17/0.39  # Training examples: 0 positive, 0 negative
% 0.17/0.39  # Parsed axioms                        : 10
% 0.17/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.39  # Initial clauses                      : 29
% 0.17/0.39  # Removed in clause preprocessing      : 1
% 0.17/0.39  # Initial clauses in saturation        : 28
% 0.17/0.39  # Processed clauses                    : 460
% 0.17/0.39  # ...of these trivial                  : 4
% 0.17/0.39  # ...subsumed                          : 114
% 0.17/0.39  # ...remaining for further processing  : 342
% 0.17/0.39  # Other redundant clauses eliminated   : 26
% 0.17/0.39  # Clauses deleted for lack of memory   : 0
% 0.17/0.39  # Backward-subsumed                    : 8
% 0.17/0.39  # Backward-rewritten                   : 204
% 0.17/0.39  # Generated clauses                    : 2037
% 0.17/0.39  # ...of the previous two non-trivial   : 1925
% 0.17/0.39  # Contextual simplify-reflections      : 6
% 0.17/0.39  # Paramodulations                      : 2001
% 0.17/0.39  # Factorizations                       : 12
% 0.17/0.39  # Equation resolutions                 : 26
% 0.17/0.39  # Propositional unsat checks           : 0
% 0.17/0.39  #    Propositional check models        : 0
% 0.17/0.39  #    Propositional check unsatisfiable : 0
% 0.17/0.39  #    Propositional clauses             : 0
% 0.17/0.39  #    Propositional clauses after purity: 0
% 0.17/0.39  #    Propositional unsat core size     : 0
% 0.17/0.39  #    Propositional preprocessing time  : 0.000
% 0.17/0.39  #    Propositional encoding time       : 0.000
% 0.17/0.39  #    Propositional solver time         : 0.000
% 0.17/0.39  #    Success case prop preproc time    : 0.000
% 0.17/0.39  #    Success case prop encoding time   : 0.000
% 0.17/0.39  #    Success case prop solver time     : 0.000
% 0.17/0.39  # Current number of processed clauses  : 96
% 0.17/0.39  #    Positive orientable unit clauses  : 35
% 0.17/0.39  #    Positive unorientable unit clauses: 0
% 0.17/0.39  #    Negative unit clauses             : 2
% 0.17/0.39  #    Non-unit-clauses                  : 59
% 0.17/0.39  # Current number of unprocessed clauses: 1496
% 0.17/0.39  # ...number of literals in the above   : 5023
% 0.17/0.39  # Current number of archived formulas  : 0
% 0.17/0.39  # Current number of archived clauses   : 241
% 0.17/0.39  # Clause-clause subsumption calls (NU) : 5881
% 0.17/0.39  # Rec. Clause-clause subsumption calls : 4923
% 0.17/0.39  # Non-unit clause-clause subsumptions  : 127
% 0.17/0.39  # Unit Clause-clause subsumption calls : 317
% 0.17/0.39  # Rewrite failures with RHS unbound    : 0
% 0.17/0.39  # BW rewrite match attempts            : 124
% 0.17/0.39  # BW rewrite match successes           : 10
% 0.17/0.39  # Condensation attempts                : 0
% 0.17/0.39  # Condensation successes               : 0
% 0.17/0.39  # Termbank termtop insertions          : 96931
% 0.17/0.39  
% 0.17/0.39  # -------------------------------------------------
% 0.17/0.39  # User time                : 0.059 s
% 0.17/0.39  # System time              : 0.007 s
% 0.17/0.39  # Total time               : 0.066 s
% 0.17/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
