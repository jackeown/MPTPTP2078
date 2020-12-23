%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1635+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:29 EST 2020

% Result     : Theorem 0.68s
% Output     : CNFRefutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   65 (1636 expanded)
%              Number of clauses        :   52 ( 606 expanded)
%              Number of leaves         :    6 ( 399 expanded)
%              Depth                    :   18
%              Number of atoms          :  308 (8291 expanded)
%              Number of equality atoms :   41 (1368 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t15_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k4_waybel_0(X1,X2) = a_2_1_waybel_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(fraenkel_a_2_1_waybel_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_waybel_0(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ? [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
                & r1_orders_2(X2,X5,X4)
                & r2_hidden(X5,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(d16_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k4_waybel_0(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                          & r1_orders_2(X1,X5,X4)
                          & r2_hidden(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => k4_waybel_0(X1,X2) = a_2_1_waybel_0(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t15_waybel_0])).

fof(c_0_7,plain,(
    ! [X15,X16] :
      ( ~ l1_orders_2(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
      | m1_subset_1(k4_waybel_0(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & l1_orders_2(esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0)))
    & k4_waybel_0(esk7_0,esk8_0) != a_2_1_waybel_0(esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X17,X18,X19,X22,X23] :
      ( ( m1_subset_1(esk4_3(X17,X18,X19),u1_struct_0(X18))
        | ~ r2_hidden(X17,a_2_1_waybel_0(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( X17 = esk4_3(X17,X18,X19)
        | ~ r2_hidden(X17,a_2_1_waybel_0(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( m1_subset_1(esk5_3(X17,X18,X19),u1_struct_0(X18))
        | ~ r2_hidden(X17,a_2_1_waybel_0(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( r1_orders_2(X18,esk5_3(X17,X18,X19),esk4_3(X17,X18,X19))
        | ~ r2_hidden(X17,a_2_1_waybel_0(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( r2_hidden(esk5_3(X17,X18,X19),X19)
        | ~ r2_hidden(X17,a_2_1_waybel_0(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( ~ m1_subset_1(X22,u1_struct_0(X18))
        | X17 != X22
        | ~ m1_subset_1(X23,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X23,X22)
        | ~ r2_hidden(X23,X19)
        | r2_hidden(X17,a_2_1_waybel_0(X18,X19))
        | v2_struct_0(X18)
        | ~ l1_orders_2(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_waybel_0])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( X1 = esk4_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X24,X25] :
      ( ( ~ r2_hidden(esk6_2(X24,X25),X24)
        | ~ r2_hidden(esk6_2(X24,X25),X25)
        | X24 = X25 )
      & ( r2_hidden(esk6_2(X24,X25),X24)
        | r2_hidden(esk6_2(X24,X25),X25)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k4_waybel_0(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( esk4_3(X1,esk7_0,esk8_0) = X1
    | ~ r2_hidden(X1,a_2_1_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_20,plain,
    ( r2_hidden(esk6_2(X1,X2),X1)
    | r2_hidden(esk6_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X6,X7,X8,X9,X11,X13] :
      ( ( m1_subset_1(esk1_4(X6,X7,X8,X9),u1_struct_0(X6))
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk1_4(X6,X7,X8,X9),X9)
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk1_4(X6,X7,X8,X9),X7)
        | ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X6))
        | ~ r1_orders_2(X6,X11,X9)
        | ~ r2_hidden(X11,X7)
        | r2_hidden(X9,X8)
        | ~ m1_subset_1(X9,u1_struct_0(X6))
        | X8 != k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_subset_1(X13,u1_struct_0(X6))
        | ~ r1_orders_2(X6,X13,esk2_3(X6,X7,X8))
        | ~ r2_hidden(X13,X7)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( m1_subset_1(esk3_3(X6,X7,X8),u1_struct_0(X6))
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r1_orders_2(X6,esk3_3(X6,X7,X8),esk2_3(X6,X7,X8))
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) )
      & ( r2_hidden(esk3_3(X6,X7,X8),X7)
        | r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k4_waybel_0(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_waybel_0])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(X3,a_2_1_waybel_0(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | X3 != X1
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X5)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,k4_waybel_0(esk7_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1)
    | a_2_1_waybel_0(esk7_0,esk8_0) = X1
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( k4_waybel_0(esk7_0,esk8_0) != a_2_1_waybel_0(esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_1_waybel_0(X1,X3))
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_22,c_0_17])])).

cnf(c_0_28,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))
    | m1_subset_1(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_4(X1,X2,k4_waybel_0(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_26,c_0_17])]),c_0_11])).

cnf(c_0_30,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,X3,X4),X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X3 != k4_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X2))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),a_2_1_waybel_0(esk7_0,X1))
    | ~ r1_orders_2(esk7_0,X2,esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_13])]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),X1),esk8_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_13])])).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,esk1_4(X1,X2,k4_waybel_0(X1,X2),X3),X3)
    | ~ r2_hidden(X3,k4_waybel_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_30,c_0_17])]),c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_3(X1,esk7_0,esk8_0),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,a_2_1_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))
    | ~ r1_orders_2(esk7_0,X1,esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_12]),c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))
    | r2_hidden(esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_24]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk7_0,esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),X1),X1)
    | ~ r2_hidden(X1,k4_waybel_0(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_12]),c_0_13])])).

cnf(c_0_39,negated_conjecture,
    ( a_2_1_waybel_0(esk7_0,esk8_0) = X1
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),X1)
    | m1_subset_1(esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),esk7_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))
    | ~ r1_orders_2(esk7_0,esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( X1 = k4_waybel_0(esk7_0,esk8_0)
    | r1_orders_2(esk7_0,esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),esk6_2(X1,k4_waybel_0(esk7_0,esk8_0))),esk6_2(X1,k4_waybel_0(esk7_0,esk8_0)))
    | r2_hidden(esk6_2(X1,k4_waybel_0(esk7_0,esk8_0)),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_20])).

cnf(c_0_42,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k4_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0),u1_struct_0(esk7_0))
    | m1_subset_1(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_39]),c_0_25])).

cnf(c_0_44,negated_conjecture,
    ( esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0) = esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_25]),c_0_19])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k4_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_42,c_0_17])]),c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,plain,
    ( r1_orders_2(X1,esk5_3(X2,X1,X3),esk4_3(X2,X1,X3))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,a_2_1_waybel_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),k4_waybel_0(esk7_0,X1))
    | ~ r1_orders_2(esk7_0,X2,esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_13])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_3(X1,esk7_0,esk8_0),esk8_0)
    | ~ r2_hidden(X1,a_2_1_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( r1_orders_2(esk7_0,esk5_3(X1,esk7_0,esk8_0),esk4_3(X1,esk7_0,esk8_0))
    | ~ r2_hidden(X1,a_2_1_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_12]),c_0_13])]),c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),k4_waybel_0(esk7_0,esk8_0))
    | ~ r1_orders_2(esk7_0,X1,esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( a_2_1_waybel_0(esk7_0,esk8_0) = X1
    | r2_hidden(esk5_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),esk7_0,esk8_0),esk8_0)
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( a_2_1_waybel_0(esk7_0,esk8_0) = X1
    | r1_orders_2(esk7_0,esk5_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),esk7_0,esk8_0),esk4_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),esk7_0,esk8_0))
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( a_2_1_waybel_0(esk7_0,esk8_0) = X1
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),k4_waybel_0(esk7_0,esk8_0))
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),X1)
    | ~ r1_orders_2(esk7_0,esk5_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),X1),esk7_0,esk8_0),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( r1_orders_2(esk7_0,esk5_3(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),esk7_0,esk8_0),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),k4_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_44]),c_0_25])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),a_2_1_waybel_0(esk7_0,X1))
    | ~ r1_orders_2(esk7_0,X2,esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_46]),c_0_13])]),c_0_15])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),k4_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_25])).

cnf(c_0_59,plain,
    ( X1 = X2
    | ~ r2_hidden(esk6_2(X1,X2),X1)
    | ~ r2_hidden(esk6_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),a_2_1_waybel_0(esk7_0,esk8_0))
    | ~ r1_orders_2(esk7_0,X1,esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0)),a_2_1_waybel_0(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_orders_2(esk7_0,esk1_4(esk7_0,esk8_0,k4_waybel_0(esk7_0,esk8_0),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))),esk6_2(a_2_1_waybel_0(esk7_0,esk8_0),k4_waybel_0(esk7_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_41]),c_0_25]),c_0_62]),
    [proof]).

%------------------------------------------------------------------------------
