%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1157+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:50 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 626 expanded)
%              Number of clauses        :   47 ( 232 expanded)
%              Number of leaves         :    9 ( 147 expanded)
%              Depth                    :   18
%              Number of atoms          :  311 (4297 expanded)
%              Number of equality atoms :   34 ( 186 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_orders_2,conjecture,(
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
              <=> r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

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

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

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
                <=> r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_orders_2])).

fof(c_0_10,plain,(
    ! [X19,X20,X21,X23,X24] :
      ( ( m1_subset_1(esk2_3(X19,X20,X21),u1_struct_0(X20))
        | ~ r2_hidden(X19,a_2_0_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( X19 = esk2_3(X19,X20,X21)
        | ~ r2_hidden(X19,a_2_0_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ r2_hidden(X23,X21)
        | r2_orders_2(X20,X23,esk2_3(X19,X20,X21))
        | ~ r2_hidden(X19,a_2_0_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( m1_subset_1(esk3_4(X19,X20,X21,X24),u1_struct_0(X20))
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_0_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( r2_hidden(esk3_4(X19,X20,X21,X24),X21)
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_0_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) )
      & ( ~ r2_orders_2(X20,esk3_4(X19,X20,X21,X24),X24)
        | ~ m1_subset_1(X24,u1_struct_0(X20))
        | X19 != X24
        | r2_hidden(X19,a_2_0_orders_2(X20,X21))
        | v2_struct_0(X20)
        | ~ v3_orders_2(X20)
        | ~ v4_orders_2(X20)
        | ~ v5_orders_2(X20)
        | ~ l1_orders_2(X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

fof(c_0_11,plain,(
    ! [X15,X16] :
      ( v1_xboole_0(X15)
      | ~ m1_subset_1(X16,X15)
      | m1_subset_1(k6_domain_1(X15,X16),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
      | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) )
    & ( r2_orders_2(esk4_0,esk5_0,esk6_0)
      | r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_13,plain,(
    ! [X26,X27] :
      ( v1_xboole_0(X26)
      | ~ m1_subset_1(X27,X26)
      | k6_domain_1(X26,X27) = k1_tarski(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_14,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
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

cnf(c_0_19,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X1),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk4_0),esk5_0) = k1_tarski(esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_28,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk3_4(esk6_0,esk4_0,X1,esk6_0),X1)
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_31,plain,
    ( r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,esk3_4(X2,X1,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X2 != X4
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk3_4(esk6_0,esk4_0,k1_tarski(esk5_0),esk6_0),k1_tarski(esk5_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ r2_orders_2(X2,esk3_4(X1,X2,X3,X1),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( esk3_4(esk6_0,esk4_0,k1_tarski(esk5_0),esk6_0) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_36,plain,(
    ! [X6,X7] :
      ( v2_struct_0(X6)
      | ~ v3_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ l1_orders_2(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | k1_orders_2(X6,X7) = a_2_0_orders_2(X6,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_37,plain,(
    ! [X32,X33,X34] :
      ( ~ r2_hidden(X32,X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(X34))
      | m1_subset_1(X32,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k1_tarski(esk5_0)))
    | ~ r2_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( r2_orders_2(X2,X1,esk2_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0)) = a_2_0_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_46,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,X4))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k1_tarski(esk5_0)))
    | r2_hidden(esk6_0,k1_orders_2(esk4_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_49,negated_conjecture,
    ( k1_orders_2(esk4_0,k1_tarski(esk5_0)) = a_2_0_orders_2(esk4_0,k1_tarski(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_27])).

cnf(c_0_50,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,k1_tarski(X2)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,k1_tarski(X2)))
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | r2_hidden(esk6_0,a_2_0_orders_2(esk4_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk2_3(esk6_0,esk4_0,k1_tarski(esk5_0)))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( esk2_3(esk6_0,esk4_0,k1_tarski(esk5_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_51]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,negated_conjecture,
    ( r2_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k6_domain_1(u1_struct_0(esk4_0),esk5_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

fof(c_0_58,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk6_0,k1_orders_2(esk4_0,k1_tarski(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_27])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_49]),c_0_51])).

fof(c_0_62,plain,(
    ! [X17] :
      ( ~ l1_orders_2(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_63,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25])).

cnf(c_0_64,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_21])]),
    [proof]).

%------------------------------------------------------------------------------
