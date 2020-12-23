%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1158+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:51 EST 2020

% Result     : Theorem 0.07s
% Output     : CNFRefutation 0.07s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 653 expanded)
%              Number of clauses        :   49 ( 241 expanded)
%              Number of leaves         :    9 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  317 (4495 expanded)
%              Number of equality atoms :   34 ( 183 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_11,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | k2_orders_2(X6,X7) = a_2_1_orders_2(X6,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

cnf(c_0_13,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X19,X20,X21,X23,X24] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( X19 = esk2_3(X19,X20,X21)
        | ~ r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X23,X21)
        | r2_orders_2(X20,esk2_3(X19,X20,X21),X23)
        | ~ r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( m1_subset_1(esk3_4(X19,X20,X21,X24),u1_struct_0(X20))
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r2_hidden(esk3_4(X19,X20,X21,X24),X21)
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ r2_orders_2(X20,X24,esk3_4(X19,X20,X21,X24))
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_1_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_16,plain,(
    ! [X26,X27] :
      ( v1_xboole_0(X26)
      | ~ m1_subset_1(X27,X26)
      | k6_domain_1(X26,X27) = k1_tarski(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)) = a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_28,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X10,X9)
        | X10 = X8
        | X9 != k1_tarski(X8) )
      & ( X11 != X8
        | r2_hidden(X11,X9)
        | X9 != k1_tarski(X8) )
      & ( ~ r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) != X12
        | X13 = k1_tarski(X12) )
      & ( r2_hidden(esk1_2(X12,X13),X13)
        | esk1_2(X12,X13) = X12
        | X13 = k1_tarski(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X1),X3)
    | r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk6_0) = k1_tarski(esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_34,plain,(
    ! [X28,X29,X30] :
      ( ~ r2_hidden(X28,X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(X30))
      | m1_subset_1(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_35,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk3_4(esk5_0,esk4_0,X1,esk5_0),X1)
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k1_tarski(esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0)))
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk3_4(esk5_0,esk4_0,k1_tarski(esk6_0),esk5_0),k1_tarski(esk6_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k1_tarski(esk6_0)))
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,k2_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_47,plain,
    ( r2_orders_2(X1,esk2_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_49,plain,
    ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ r2_orders_2(X2,X1,esk3_4(X1,X2,X3,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( esk3_4(esk5_0,esk4_0,k1_tarski(esk6_0),esk5_0) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r2_orders_2(X1,esk2_3(X2,X1,k1_tarski(X3)),X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,k1_tarski(X3)))
    | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk5_0,a_2_1_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_30]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_37]),c_0_51])).

cnf(c_0_54,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_55,negated_conjecture,
    ( r2_orders_2(esk4_0,esk2_3(esk5_0,esk4_0,k1_tarski(esk6_0)),esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_37])).

cnf(c_0_56,negated_conjecture,
    ( esk2_3(esk5_0,esk4_0,k1_tarski(esk6_0)) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk6_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_57])).

fof(c_0_59,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k2_orders_2(esk4_0,k1_tarski(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( k2_orders_2(esk4_0,k1_tarski(esk6_0)) = a_2_1_orders_2(esk4_0,k1_tarski(esk6_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_31])).

cnf(c_0_62,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_53])).

fof(c_0_64,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_23])).

cnf(c_0_66,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
