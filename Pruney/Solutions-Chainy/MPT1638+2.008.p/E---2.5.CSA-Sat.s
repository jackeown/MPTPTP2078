%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:10 EST 2020

% Result     : CounterSatisfiable 0.46s
% Output     : Saturation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  142 (3678 expanded)
%              Number of clauses        :  127 (1948 expanded)
%              Number of leaves         :    7 ( 852 expanded)
%              Depth                    :   26
%              Number of atoms          :  591 (26403 expanded)
%              Number of equality atoms :  470 (18848 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t18_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k6_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(c_0_7,plain,(
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

cnf(c_0_8,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_9,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | esk1_3(X1,X2,X3) = X1
    | esk1_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X4
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X3
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X1
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_14,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X1)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X1)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X1)) = X2
    | k2_tarski(X3,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])]),
    [final]).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_18,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X1)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X1)) = X3
    | k2_tarski(X3,X1) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])]),
    [final]).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])]),
    [final]).

cnf(c_0_20,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X1)) = X3
    | k2_tarski(X3,X1) = k2_tarski(X1,X2)
    | ~ r2_hidden(X2,k2_tarski(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_21,plain,
    ( esk1_3(X1,X2,k2_tarski(X1,X1)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_18]),c_0_19])])]),
    [final]).

cnf(c_0_22,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X1)),k2_tarski(X4,X1)) = X4
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X1))) = k2_tarski(X4,X1)
    | esk1_3(X2,X3,k2_tarski(X4,X1)) = X2
    | esk1_3(X2,X3,k2_tarski(X4,X1)) = X3
    | k2_tarski(X4,X1) = k2_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_20,c_0_10]),
    [final]).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k2_tarski(X1,X2)
    | ~ r2_hidden(X2,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21]),
    [final]).

cnf(c_0_24,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X3)) = X2
    | esk1_3(X1,X1,k2_tarski(X2,X3)) = X3
    | esk1_3(X1,X1,k2_tarski(X2,X3)) = X1
    | k2_tarski(X2,X3) = k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])]),
    [final]).

cnf(c_0_25,plain,
    ( k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X1))) = k2_tarski(X4,X1)
    | esk1_3(X2,X3,k2_tarski(X4,X1)) = X3
    | esk1_3(X2,X3,k2_tarski(X4,X1)) = X2
    | k2_tarski(X4,X1) = k2_tarski(X2,X3)
    | esk1_3(X2,X3,k2_tarski(X4,X1)) != X4 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_22]),c_0_19])]),
    [final]).

cnf(c_0_26,plain,
    ( k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
    | esk1_3(X2,X3,k2_tarski(X1,X1)) = X2
    | esk1_3(X2,X3,k2_tarski(X1,X1)) = X3
    | k2_tarski(X1,X1) = k2_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_23,c_0_10]),
    [final]).

cnf(c_0_27,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X3,X3) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])]),
    [final]).

cnf(c_0_28,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])]),
    [final]).

cnf(c_0_29,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X4,X5,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X4
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X5
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | k2_tarski(X3,X3) = k2_tarski(X4,X5) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),
    [final]).

cnf(c_0_30,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(X3,X4,k2_tarski(X2,X2))
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X3
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X4
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X3,X4)
    | k2_tarski(X2,X2) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_31,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(X3,X3,k2_tarski(X2,X2))
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | esk1_3(X3,X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X3) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_30])]),
    [final]).

cnf(c_0_32,plain,
    ( k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
    | esk1_3(X3,X3,k2_tarski(X1,X1)) = X3
    | esk1_3(X2,X2,k2_tarski(X1,X1)) = X2
    | esk1_3(X2,X2,k2_tarski(X1,X1)) = X3
    | k2_tarski(X1,X1) = k2_tarski(X2,X2)
    | k2_tarski(X1,X1) = k2_tarski(X3,X3) ),
    inference(spm,[status(thm)],[c_0_26,c_0_31])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X1,X1))) = k2_tarski(X1,X1)
    | esk1_3(X2,X2,k2_tarski(X1,X1)) = X2
    | k2_tarski(X1,X1) = k2_tarski(X2,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_32])]),
    [final]).

cnf(c_0_34,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(X3,X3,k2_tarski(X2,X2))
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X3)
    | ~ r2_hidden(X3,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_31]),
    [final]).

cnf(c_0_35,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | r2_hidden(esk1_3(X1,X1,k2_tarski(X2,X2)),k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33]),
    [final]).

cnf(c_0_36,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(esk1_3(X3,X3,k2_tarski(X2,X2)),esk1_3(X3,X3,k2_tarski(X2,X2)),k2_tarski(X2,X2))
    | k2_tarski(esk1_3(X3,X3,k2_tarski(X2,X2)),esk1_3(X3,X3,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | esk1_3(X3,X3,k2_tarski(X2,X2)) = X3
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X3,X3)
    | k2_tarski(X2,X2) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_37,plain,
    ( k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X1,X1,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | esk1_3(X3,X3,k2_tarski(X2,X2)) = X3
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X3,X3)
    | k2_tarski(X2,X2) = k2_tarski(X1,X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_36]),c_0_35]),c_0_31])).

cnf(c_0_38,plain,
    ( k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X1,X1,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X3)
    | ~ r2_hidden(X3,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_37])).

cnf(c_0_39,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | k2_tarski(esk1_3(X4,X4,k2_tarski(X3,X3)),esk1_3(X4,X4,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X4,X4,k2_tarski(X3,X3)) = X4
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | k2_tarski(X3,X3) = k2_tarski(X4,X4) ),
    inference(spm,[status(thm)],[c_0_38,c_0_10])).

fof(c_0_40,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k6_waybel_0(X1,X2))
                <=> r1_orders_2(X1,X2,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_waybel_0])).

cnf(c_0_41,plain,
    ( k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X1,X1,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X1) ),
    inference(ef,[status(thm)],[c_0_39]),
    [final]).

cnf(c_0_42,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = esk1_3(X4,X5,k2_tarski(X3,X3))
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X4
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | k2_tarski(X3,X3) = k2_tarski(X4,X5)
    | k2_tarski(X3,X3) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_29]),
    [final]).

fof(c_0_43,plain,(
    ! [X18] :
      ( ~ l1_orders_2(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( ~ r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))
      | ~ r1_orders_2(esk2_0,esk3_0,esk4_0) )
    & ( r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))
      | r1_orders_2(esk2_0,esk3_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])).

cnf(c_0_45,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X4,X4,k2_tarski(X3,X3)) = X4
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X4
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | k2_tarski(X3,X3) = k2_tarski(X4,X4) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_46,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | ~ v1_xboole_0(u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

fof(c_0_49,plain,(
    ! [X19,X20] :
      ( v1_xboole_0(X19)
      | ~ m1_subset_1(X20,X19)
      | k6_domain_1(X19,X20) = k1_tarski(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_50,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_51,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X4)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X4
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | ~ r2_hidden(X2,k2_tarski(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_11]),
    [final]).

cnf(c_0_52,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X4,X4,k2_tarski(X3,X3)) = X4
    | k2_tarski(X3,X3) = k2_tarski(X4,X4)
    | k2_tarski(X3,X3) = k2_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_45]),c_0_30])).

cnf(c_0_53,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X2)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X2)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X2)) = X1
    | k2_tarski(X3,X2) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).

fof(c_0_54,plain,(
    ! [X16,X17] :
      ( v1_xboole_0(X16)
      | ~ m1_subset_1(X17,X16)
      | m1_subset_1(k6_domain_1(X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X1
    | esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5))) = k2_tarski(X4,X5)
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X2
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X3
    | k2_tarski(X4,X5) = k2_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_51,c_0_10]),
    [final]).

cnf(c_0_61,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | k2_tarski(X3,X3) = k2_tarski(X4,X4)
    | ~ r2_hidden(X4,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_52])).

cnf(c_0_62,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X2)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X2)) = X3
    | k2_tarski(X3,X2) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_53]),c_0_15])]),
    [final]).

cnf(c_0_63,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X2,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27]),
    [final]).

cnf(c_0_64,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X3
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_27]),
    [final]).

cnf(c_0_65,plain,
    ( esk1_3(X1,X2,k2_tarski(X2,X1)) = X2
    | k2_tarski(X2,X1) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_18])])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54]),
    [final]).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),
    [final]).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_70,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59]),
    [final]).

cnf(c_0_71,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5))) = k2_tarski(X4,X5)
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X3
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X2
    | k2_tarski(X4,X5) = k2_tarski(X2,X3)
    | ~ r2_hidden(X1,k2_tarski(X4,X5)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_60]),
    [final]).

cnf(c_0_72,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | k2_tarski(esk1_3(X4,X5,k2_tarski(X3,X3)),esk1_3(X4,X5,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X4
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X5
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | k2_tarski(X3,X3) = k2_tarski(X4,X5) ),
    inference(spm,[status(thm)],[c_0_61,c_0_10])).

cnf(c_0_73,plain,
    ( esk1_3(X1,X2,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_62]),c_0_19])])]),
    [final]).

cnf(c_0_74,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X4)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X4
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11]),
    [final]).

cnf(c_0_75,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X3)) = X3
    | esk1_3(X1,X1,k2_tarski(X2,X3)) = X2
    | k2_tarski(X2,X3) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_24]),
    [final]).

cnf(c_0_76,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X4
    | esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X1
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X4))) = k2_tarski(X4,X4)
    | esk1_3(X2,X3,k2_tarski(X4,X4)) = X2
    | esk1_3(X2,X3,k2_tarski(X4,X4)) = X3
    | k2_tarski(X4,X4) = k2_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_10])).

cnf(c_0_77,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X3)),X4,k2_tarski(X3,X3)) = X3
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X3)),X4,k2_tarski(X3,X3)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),X4) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | k2_tarski(X3,X3) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_64,c_0_10])).

cnf(c_0_78,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X2)) = X3
    | k2_tarski(X3,X2) = k2_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_62]),
    [final]).

cnf(c_0_79,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_65]),c_0_19])]),
    [final]).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_81,negated_conjecture,
    ( m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_69]),c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k2_tarski(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_67]),c_0_68]),
    [final]).

cnf(c_0_83,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk4_0) = k2_tarski(esk4_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_69]),c_0_68]),
    [final]).

cnf(c_0_84,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X5
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X6
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | k2_tarski(X3,X4) = k2_tarski(X5,X6) ),
    inference(spm,[status(thm)],[c_0_71,c_0_10]),
    [final]).

cnf(c_0_85,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X3,X3) = k2_tarski(X1,X2) ),
    inference(ef,[status(thm)],[c_0_72]),
    [final]).

cnf(c_0_86,plain,
    ( k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X3,X4,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X3
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X4
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_33]),c_0_27]),
    [final]).

cnf(c_0_87,plain,
    ( k2_tarski(X1,X1) = k2_tarski(X2,X1)
    | ~ r2_hidden(X2,k2_tarski(X1,X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_73]),
    [final]).

cnf(c_0_88,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = X2
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_28]),
    [final]).

cnf(c_0_89,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X5
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X4
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X3
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_74,c_0_10]),
    [final]).

cnf(c_0_90,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_10]),
    [final]).

cnf(c_0_91,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4)) = X1
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X4))) = k2_tarski(X4,X4)
    | esk1_3(X2,X3,k2_tarski(X4,X4)) = X3
    | esk1_3(X2,X3,k2_tarski(X4,X4)) = X2
    | k2_tarski(X4,X4) = k2_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_76]),c_0_19])]),c_0_27]),
    [final]).

cnf(c_0_92,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X3)),X4,k2_tarski(X3,X3)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),X4) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X3,X3) = k2_tarski(X1,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_77]),c_0_19])]),c_0_27]),
    [final]).

cnf(c_0_93,plain,
    ( esk1_3(X1,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79]),
    [final]).

cnf(c_0_94,plain,
    ( esk1_3(X1,X2,k2_tarski(X1,X3)) = X3
    | k2_tarski(X1,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X2,k2_tarski(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_79]),
    [final]).

cnf(c_0_95,plain,
    ( esk1_3(X1,X2,k2_tarski(X2,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X2,X3)) = X3
    | esk1_3(X1,X2,k2_tarski(X2,X3)) = X1
    | k2_tarski(X2,X3) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).

cnf(c_0_96,plain,
    ( esk1_3(X1,X2,k2_tarski(X1,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X1,X3)) = X3
    | esk1_3(X1,X2,k2_tarski(X1,X3)) = X2
    | k2_tarski(X1,X3) = k2_tarski(X1,X2) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).

cnf(c_0_97,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X1)) = X1
    | esk1_3(X1,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X2,X1) = k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).

cnf(c_0_98,plain,
    ( esk1_3(X1,X1,k2_tarski(X1,X2)) = X1
    | esk1_3(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X2) = k2_tarski(X1,X1) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_80])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k6_domain_1(u1_struct_0(esk2_0),esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_81])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_80,c_0_82]),
    [final]).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_81,c_0_83]),
    [final]).

cnf(c_0_103,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X6
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X5,X6)
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) != X4 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_84]),c_0_15])]),
    [final]).

cnf(c_0_104,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X6
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X5,X6)
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X5,X6,k2_tarski(X3,X4)) != X4 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_84]),c_0_15])]),
    [final]).

cnf(c_0_105,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X6
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X5,X6)
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) != X3 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_84]),c_0_19])]),
    [final]).

cnf(c_0_106,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X6
    | esk1_3(X5,X6,k2_tarski(X3,X4)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X5,X6)
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X5,X6,k2_tarski(X3,X4)) != X3 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_84]),c_0_19])]),
    [final]).

cnf(c_0_107,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | X4 = esk1_3(X1,X2,k2_tarski(X3,X3))
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X4,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_85]),
    [final]).

cnf(c_0_108,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | X3 = esk1_3(X1,X1,k2_tarski(X2,X2))
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | ~ r2_hidden(X3,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_41]),
    [final]).

cnf(c_0_109,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X4,X4,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | esk1_3(X4,X4,k2_tarski(X3,X3)) = X4
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | k2_tarski(X3,X3) = k2_tarski(X4,X4) ),
    inference(spm,[status(thm)],[c_0_33,c_0_29]),
    [final]).

cnf(c_0_110,plain,
    ( k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X3,X3,k2_tarski(X2,X2))) = k2_tarski(X2,X2)
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | esk1_3(X3,X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X3) ),
    inference(spm,[status(thm)],[c_0_33,c_0_86]),
    [final]).

cnf(c_0_111,plain,
    ( esk1_3(X1,esk1_3(X2,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3)) = X1
    | k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X2,X2,k2_tarski(X3,X3)) = X2
    | k2_tarski(X3,X3) = k2_tarski(X2,X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_86]),
    [final]).

cnf(c_0_112,plain,
    ( esk1_3(esk1_3(X1,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2)) = X3
    | k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),X3) = k2_tarski(X2,X2)
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_86]),
    [final]).

cnf(c_0_113,plain,
    ( k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X3,X3))) = k2_tarski(X3,X3)
    | esk1_3(X2,X2,k2_tarski(X3,X3)) = X2
    | k2_tarski(X3,X3) = k2_tarski(X2,X2)
    | ~ r2_hidden(X1,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_86]),
    [final]).

cnf(c_0_114,plain,
    ( k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),X3) = k2_tarski(X2,X2)
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | ~ r2_hidden(X3,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_86]),
    [final]).

cnf(c_0_115,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(X3,X4,k2_tarski(X2,X2))
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X4
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X4)
    | ~ r2_hidden(X3,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_30]),
    [final]).

cnf(c_0_116,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(X3,X4,k2_tarski(X2,X2))
    | esk1_3(X1,X1,k2_tarski(X2,X2)) = X1
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X3
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | k2_tarski(X2,X2) = k2_tarski(X3,X4)
    | ~ r2_hidden(X4,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_30]),
    [final]).

cnf(c_0_117,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = esk1_3(X4,X5,k2_tarski(X3,X3))
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X4
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | k2_tarski(X3,X3) = k2_tarski(X4,X5)
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X2,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_29]),
    [final]).

cnf(c_0_118,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X3)) = esk1_3(X4,X5,k2_tarski(X3,X3))
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X4
    | esk1_3(X4,X5,k2_tarski(X3,X3)) = X5
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | k2_tarski(X3,X3) = k2_tarski(X4,X5)
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_29]),
    [final]).

cnf(c_0_119,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X2)) = esk1_3(X3,X4,k2_tarski(X2,X2))
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X3
    | esk1_3(X3,X4,k2_tarski(X2,X2)) = X4
    | k2_tarski(X2,X2) = k2_tarski(X3,X4)
    | k2_tarski(X2,X2) = k2_tarski(X1,X1)
    | ~ r2_hidden(X1,k2_tarski(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_29]),
    [final]).

cnf(c_0_120,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X3
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X5
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) != X4 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_89]),c_0_15])]),
    [final]).

cnf(c_0_121,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X4
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X5
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) != X3 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_89]),c_0_19])]),
    [final]).

cnf(c_0_122,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X4
    | esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X1
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5))) = k2_tarski(X4,X5)
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X3
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X2
    | k2_tarski(X4,X5) = k2_tarski(X2,X3)
    | esk1_3(X2,X3,k2_tarski(X4,X5)) != X5 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_60]),c_0_15])]),
    [final]).

cnf(c_0_123,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X5
    | esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5)) = X1
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5))) = k2_tarski(X4,X5)
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X3
    | esk1_3(X2,X3,k2_tarski(X4,X5)) = X2
    | k2_tarski(X4,X5) = k2_tarski(X2,X3)
    | esk1_3(X2,X3,k2_tarski(X4,X5)) != X4 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_60]),c_0_19])]),
    [final]).

cnf(c_0_124,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X3
    | esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | ~ r2_hidden(X5,k2_tarski(X3,X4)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_89]),
    [final]).

cnf(c_0_125,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X4
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) != X3 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_90]),c_0_19])]),
    [final]).

cnf(c_0_126,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4)) = X3
    | k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) != X4 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_90]),c_0_15])]),
    [final]).

cnf(c_0_127,plain,
    ( k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X4))) = k2_tarski(X4,X4)
    | esk1_3(X2,X3,k2_tarski(X4,X4)) = X2
    | esk1_3(X2,X3,k2_tarski(X4,X4)) = X3
    | k2_tarski(X4,X4) = k2_tarski(X2,X3)
    | ~ r2_hidden(X1,k2_tarski(X4,X4)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_91]),
    [final]).

cnf(c_0_128,plain,
    ( k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),X4) = k2_tarski(X3,X3)
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X3)) = X2
    | k2_tarski(X3,X3) = k2_tarski(X1,X2)
    | ~ r2_hidden(X4,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_92]),
    [final]).

cnf(c_0_129,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X3,k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,esk1_3(X1,X2,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_10]),c_0_79]),
    [final]).

cnf(c_0_130,plain,
    ( esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X4,k2_tarski(X3,X4)) = X3
    | k2_tarski(X4,esk1_3(X1,X2,k2_tarski(X3,X4))) = k2_tarski(X3,X4)
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_10]),c_0_79]),
    [final]).

cnf(c_0_131,plain,
    ( esk1_3(X1,esk1_3(X2,X3,k2_tarski(X1,X4)),k2_tarski(X1,X4)) = X4
    | k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X1,X4))) = k2_tarski(X1,X4)
    | esk1_3(X2,X3,k2_tarski(X1,X4)) = X2
    | esk1_3(X2,X3,k2_tarski(X1,X4)) = X3
    | k2_tarski(X1,X4) = k2_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_94,c_0_10]),
    [final]).

cnf(c_0_132,plain,
    ( esk1_3(X1,X2,k2_tarski(X2,X3)) = X1
    | esk1_3(X1,X2,k2_tarski(X2,X3)) = X3
    | k2_tarski(X2,X3) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_95]),c_0_19])]),
    [final]).

cnf(c_0_133,plain,
    ( esk1_3(X1,X2,k2_tarski(X1,X3)) = X2
    | esk1_3(X1,X2,k2_tarski(X1,X3)) = X3
    | k2_tarski(X1,X3) = k2_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_96]),c_0_19])]),
    [final]).

cnf(c_0_134,plain,
    ( esk1_3(X1,X1,k2_tarski(X2,X1)) = X2
    | k2_tarski(X2,X1) = k2_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_97]),c_0_15])]),
    [final]).

cnf(c_0_135,plain,
    ( esk1_3(X1,X1,k2_tarski(X1,X2)) = X2
    | k2_tarski(X1,X2) = k2_tarski(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_98]),c_0_19])]),
    [final]).

cnf(c_0_136,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk3_0,esk3_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_99,c_0_82]),
    [final]).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk4_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_100,c_0_83]),
    [final]).

cnf(c_0_138,negated_conjecture,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk3_0,esk3_0)) = k2_tarski(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk3_0))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_101]),
    [final]).

cnf(c_0_139,negated_conjecture,
    ( k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk4_0,esk4_0)) = k2_tarski(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_70,c_0_102]),
    [final]).

cnf(c_0_140,negated_conjecture,
    ( r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))
    | r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).

cnf(c_0_141,negated_conjecture,
    ( ~ r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))
    | ~ r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_44]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.61  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S002I
% 0.46/0.61  # and selection function SelectNegativeLiterals.
% 0.46/0.61  #
% 0.46/0.61  # Preprocessing time       : 0.027 s
% 0.46/0.61  # Presaturation interreduction done
% 0.46/0.61  
% 0.46/0.61  # No proof found!
% 0.46/0.61  # SZS status CounterSatisfiable
% 0.46/0.61  # SZS output start Saturation
% 0.46/0.61  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.46/0.61  fof(t18_waybel_0, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k6_waybel_0(X1,X2))<=>r1_orders_2(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_waybel_0)).
% 0.46/0.61  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.46/0.61  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.46/0.61  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.46/0.61  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.46/0.61  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.46/0.61  fof(c_0_7, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.46/0.61  cnf(c_0_8, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.61  cnf(c_0_9, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_8]), ['final']).
% 0.46/0.61  cnf(c_0_10, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|esk1_3(X1,X2,X3)=X1|esk1_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.46/0.61  cnf(c_0_11, plain, (esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X4|esk1_3(X1,X2,k2_tarski(X3,X4))=X3|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.46/0.61  cnf(c_0_12, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.61  cnf(c_0_13, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X1|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.46/0.61  cnf(c_0_14, plain, (esk1_3(X1,X2,k2_tarski(X3,X1))=X3|esk1_3(X1,X2,k2_tarski(X3,X1))=X1|esk1_3(X1,X2,k2_tarski(X3,X1))=X2|k2_tarski(X3,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).
% 0.46/0.61  cnf(c_0_15, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_12])]), ['final']).
% 0.46/0.61  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.61  cnf(c_0_17, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.46/0.61  cnf(c_0_18, plain, (esk1_3(X1,X2,k2_tarski(X3,X1))=X2|esk1_3(X1,X2,k2_tarski(X3,X1))=X3|k2_tarski(X3,X1)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])]), ['final']).
% 0.46/0.61  cnf(c_0_19, plain, (r2_hidden(X1,k2_tarski(X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])]), ['final']).
% 0.46/0.61  cnf(c_0_20, plain, (esk1_3(X1,X2,k2_tarski(X3,X1))=X3|k2_tarski(X3,X1)=k2_tarski(X1,X2)|~r2_hidden(X2,k2_tarski(X3,X1))), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.46/0.61  cnf(c_0_21, plain, (esk1_3(X1,X2,k2_tarski(X1,X1))=X2|k2_tarski(X1,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_18]), c_0_19])])]), ['final']).
% 0.46/0.61  cnf(c_0_22, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X1)),k2_tarski(X4,X1))=X4|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X1)))=k2_tarski(X4,X1)|esk1_3(X2,X3,k2_tarski(X4,X1))=X2|esk1_3(X2,X3,k2_tarski(X4,X1))=X3|k2_tarski(X4,X1)=k2_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_20, c_0_10]), ['final']).
% 0.46/0.61  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k2_tarski(X1,X2)|~r2_hidden(X2,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_17, c_0_21]), ['final']).
% 0.46/0.61  cnf(c_0_24, plain, (esk1_3(X1,X1,k2_tarski(X2,X3))=X2|esk1_3(X1,X1,k2_tarski(X2,X3))=X3|esk1_3(X1,X1,k2_tarski(X2,X3))=X1|k2_tarski(X2,X3)=k2_tarski(X1,X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])]), ['final']).
% 0.46/0.61  cnf(c_0_25, plain, (k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X1)))=k2_tarski(X4,X1)|esk1_3(X2,X3,k2_tarski(X4,X1))=X3|esk1_3(X2,X3,k2_tarski(X4,X1))=X2|k2_tarski(X4,X1)=k2_tarski(X2,X3)|esk1_3(X2,X3,k2_tarski(X4,X1))!=X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_22]), c_0_19])]), ['final']).
% 0.46/0.61  cnf(c_0_26, plain, (k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X1,X1)))=k2_tarski(X1,X1)|esk1_3(X2,X3,k2_tarski(X1,X1))=X2|esk1_3(X2,X3,k2_tarski(X1,X1))=X3|k2_tarski(X1,X1)=k2_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_23, c_0_10]), ['final']).
% 0.46/0.61  cnf(c_0_27, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=X3|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|k2_tarski(X3,X3)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])]), ['final']).
% 0.46/0.61  cnf(c_0_28, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=X1|esk1_3(X1,X1,k2_tarski(X2,X2))=X2|k2_tarski(X2,X2)=k2_tarski(X1,X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])]), ['final']).
% 0.46/0.61  cnf(c_0_29, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X4,X5,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X4,X5,k2_tarski(X3,X3))=X4|esk1_3(X4,X5,k2_tarski(X3,X3))=X5|k2_tarski(X3,X3)=k2_tarski(X1,X2)|k2_tarski(X3,X3)=k2_tarski(X4,X5)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), ['final']).
% 0.46/0.61  cnf(c_0_30, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(X3,X4,k2_tarski(X2,X2))|esk1_3(X3,X4,k2_tarski(X2,X2))=X3|esk1_3(X3,X4,k2_tarski(X2,X2))=X4|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X3,X4)|k2_tarski(X2,X2)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.46/0.61  cnf(c_0_31, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(X3,X3,k2_tarski(X2,X2))|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|esk1_3(X3,X3,k2_tarski(X2,X2))=X3|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X3)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_30])]), ['final']).
% 0.46/0.61  cnf(c_0_32, plain, (k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X1,X1)))=k2_tarski(X1,X1)|esk1_3(X3,X3,k2_tarski(X1,X1))=X3|esk1_3(X2,X2,k2_tarski(X1,X1))=X2|esk1_3(X2,X2,k2_tarski(X1,X1))=X3|k2_tarski(X1,X1)=k2_tarski(X2,X2)|k2_tarski(X1,X1)=k2_tarski(X3,X3)), inference(spm,[status(thm)],[c_0_26, c_0_31])).
% 0.46/0.61  cnf(c_0_33, plain, (k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X1,X1)))=k2_tarski(X1,X1)|esk1_3(X2,X2,k2_tarski(X1,X1))=X2|k2_tarski(X1,X1)=k2_tarski(X2,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_32])]), ['final']).
% 0.46/0.61  cnf(c_0_34, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(X3,X3,k2_tarski(X2,X2))|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X3)|~r2_hidden(X3,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_17, c_0_31]), ['final']).
% 0.46/0.62  cnf(c_0_35, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X1)|r2_hidden(esk1_3(X1,X1,k2_tarski(X2,X2)),k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_15, c_0_33]), ['final']).
% 0.46/0.62  cnf(c_0_36, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(esk1_3(X3,X3,k2_tarski(X2,X2)),esk1_3(X3,X3,k2_tarski(X2,X2)),k2_tarski(X2,X2))|k2_tarski(esk1_3(X3,X3,k2_tarski(X2,X2)),esk1_3(X3,X3,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|esk1_3(X3,X3,k2_tarski(X2,X2))=X3|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X3,X3)|k2_tarski(X2,X2)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.46/0.62  cnf(c_0_37, plain, (k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X1,X1,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|esk1_3(X3,X3,k2_tarski(X2,X2))=X3|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X3,X3)|k2_tarski(X2,X2)=k2_tarski(X1,X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_36]), c_0_35]), c_0_31])).
% 0.46/0.62  cnf(c_0_38, plain, (k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X1,X1,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X3)|~r2_hidden(X3,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_17, c_0_37])).
% 0.46/0.62  cnf(c_0_39, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|k2_tarski(esk1_3(X4,X4,k2_tarski(X3,X3)),esk1_3(X4,X4,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X4,X4,k2_tarski(X3,X3))=X4|k2_tarski(X3,X3)=k2_tarski(X1,X2)|k2_tarski(X3,X3)=k2_tarski(X4,X4)), inference(spm,[status(thm)],[c_0_38, c_0_10])).
% 0.46/0.62  fof(c_0_40, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,k6_waybel_0(X1,X2))<=>r1_orders_2(X1,X2,X3)))))), inference(assume_negation,[status(cth)],[t18_waybel_0])).
% 0.46/0.62  cnf(c_0_41, plain, (k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X1,X1,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X1)), inference(ef,[status(thm)],[c_0_39]), ['final']).
% 0.46/0.62  cnf(c_0_42, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=esk1_3(X4,X5,k2_tarski(X3,X3))|esk1_3(X4,X5,k2_tarski(X3,X3))=X4|esk1_3(X4,X5,k2_tarski(X3,X3))=X5|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|k2_tarski(X3,X3)=k2_tarski(X4,X5)|k2_tarski(X3,X3)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_29]), ['final']).
% 0.46/0.62  fof(c_0_43, plain, ![X18]:(~l1_orders_2(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.46/0.62  fof(c_0_44, negated_conjecture, ((~v2_struct_0(esk2_0)&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))|~r1_orders_2(esk2_0,esk3_0,esk4_0))&(r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))|r1_orders_2(esk2_0,esk3_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_40])])])])).
% 0.46/0.62  cnf(c_0_45, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X4,X4,k2_tarski(X3,X3))=X4|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X4|k2_tarski(X3,X3)=k2_tarski(X1,X2)|k2_tarski(X3,X3)=k2_tarski(X4,X4)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.46/0.62  fof(c_0_46, plain, ![X15]:(v2_struct_0(X15)|~l1_struct_0(X15)|~v1_xboole_0(u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.46/0.62  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_43]), ['final']).
% 0.46/0.62  cnf(c_0_48, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.46/0.62  fof(c_0_49, plain, ![X19, X20]:(v1_xboole_0(X19)|~m1_subset_1(X20,X19)|k6_domain_1(X19,X20)=k1_tarski(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.46/0.62  fof(c_0_50, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.46/0.62  cnf(c_0_51, plain, (esk1_3(X1,X2,k2_tarski(X3,X4))=X3|esk1_3(X1,X2,k2_tarski(X3,X4))=X4|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X1,X2)|~r2_hidden(X2,k2_tarski(X3,X4))), inference(spm,[status(thm)],[c_0_17, c_0_11]), ['final']).
% 0.46/0.62  cnf(c_0_52, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X4,X4,k2_tarski(X3,X3))=X4|k2_tarski(X3,X3)=k2_tarski(X4,X4)|k2_tarski(X3,X3)=k2_tarski(X1,X2)), inference(csr,[status(thm)],[inference(ef,[status(thm)],[c_0_45]), c_0_30])).
% 0.46/0.62  cnf(c_0_53, plain, (esk1_3(X1,X2,k2_tarski(X3,X2))=X3|esk1_3(X1,X2,k2_tarski(X3,X2))=X2|esk1_3(X1,X2,k2_tarski(X3,X2))=X1|k2_tarski(X3,X2)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).
% 0.46/0.62  fof(c_0_54, plain, ![X16, X17]:(v1_xboole_0(X16)|~m1_subset_1(X17,X16)|m1_subset_1(k6_domain_1(X16,X17),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.46/0.62  cnf(c_0_55, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46]), ['final']).
% 0.46/0.62  cnf(c_0_56, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_48]), ['final']).
% 0.46/0.62  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.46/0.62  cnf(c_0_58, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.46/0.62  cnf(c_0_59, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.46/0.62  cnf(c_0_60, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X1|esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X5|esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X4|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5)))=k2_tarski(X4,X5)|esk1_3(X2,X3,k2_tarski(X4,X5))=X2|esk1_3(X2,X3,k2_tarski(X4,X5))=X3|k2_tarski(X4,X5)=k2_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_51, c_0_10]), ['final']).
% 0.46/0.62  cnf(c_0_61, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|k2_tarski(X3,X3)=k2_tarski(X1,X2)|k2_tarski(X3,X3)=k2_tarski(X4,X4)|~r2_hidden(X4,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_17, c_0_52])).
% 0.46/0.62  cnf(c_0_62, plain, (esk1_3(X1,X2,k2_tarski(X3,X2))=X1|esk1_3(X1,X2,k2_tarski(X3,X2))=X3|k2_tarski(X3,X2)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_53]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_63, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_tarski(X1,X2)|~r2_hidden(X2,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_17, c_0_27]), ['final']).
% 0.46/0.62  cnf(c_0_64, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X3|k2_tarski(X3,X3)=k2_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_13, c_0_27]), ['final']).
% 0.46/0.62  cnf(c_0_65, plain, (esk1_3(X1,X2,k2_tarski(X2,X1))=X2|k2_tarski(X2,X1)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_18])])).
% 0.46/0.62  cnf(c_0_66, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54]), ['final']).
% 0.46/0.62  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.46/0.62  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), ['final']).
% 0.46/0.62  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.46/0.62  cnf(c_0_70, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_58, c_0_59]), ['final']).
% 0.46/0.62  cnf(c_0_71, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X4|esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X5|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5)))=k2_tarski(X4,X5)|esk1_3(X2,X3,k2_tarski(X4,X5))=X3|esk1_3(X2,X3,k2_tarski(X4,X5))=X2|k2_tarski(X4,X5)=k2_tarski(X2,X3)|~r2_hidden(X1,k2_tarski(X4,X5))), inference(spm,[status(thm)],[c_0_13, c_0_60]), ['final']).
% 0.46/0.62  cnf(c_0_72, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|k2_tarski(esk1_3(X4,X5,k2_tarski(X3,X3)),esk1_3(X4,X5,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X4,X5,k2_tarski(X3,X3))=X4|esk1_3(X4,X5,k2_tarski(X3,X3))=X5|k2_tarski(X3,X3)=k2_tarski(X1,X2)|k2_tarski(X3,X3)=k2_tarski(X4,X5)), inference(spm,[status(thm)],[c_0_61, c_0_10])).
% 0.46/0.62  cnf(c_0_73, plain, (esk1_3(X1,X2,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_62]), c_0_19])])]), ['final']).
% 0.46/0.62  cnf(c_0_74, plain, (esk1_3(X1,X2,k2_tarski(X3,X4))=X3|esk1_3(X1,X2,k2_tarski(X3,X4))=X4|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|k2_tarski(X3,X4)=k2_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X3,X4))), inference(spm,[status(thm)],[c_0_13, c_0_11]), ['final']).
% 0.46/0.62  cnf(c_0_75, plain, (esk1_3(X1,X1,k2_tarski(X2,X3))=X3|esk1_3(X1,X1,k2_tarski(X2,X3))=X2|k2_tarski(X2,X3)=k2_tarski(X1,X1)|~r2_hidden(X1,k2_tarski(X2,X3))), inference(spm,[status(thm)],[c_0_17, c_0_24]), ['final']).
% 0.46/0.62  cnf(c_0_76, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4))=X4|esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4))=X1|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X4)))=k2_tarski(X4,X4)|esk1_3(X2,X3,k2_tarski(X4,X4))=X2|esk1_3(X2,X3,k2_tarski(X4,X4))=X3|k2_tarski(X4,X4)=k2_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_63, c_0_10])).
% 0.46/0.62  cnf(c_0_77, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X3)),X4,k2_tarski(X3,X3))=X3|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X3)),X4,k2_tarski(X3,X3))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),X4)=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|k2_tarski(X3,X3)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_64, c_0_10])).
% 0.46/0.62  cnf(c_0_78, plain, (esk1_3(X1,X2,k2_tarski(X3,X2))=X3|k2_tarski(X3,X2)=k2_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X3,X2))), inference(spm,[status(thm)],[c_0_13, c_0_62]), ['final']).
% 0.46/0.62  cnf(c_0_79, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_65]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_80, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])).
% 0.46/0.62  cnf(c_0_81, negated_conjecture, (m1_subset_1(k6_domain_1(u1_struct_0(esk2_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_69]), c_0_68])).
% 0.46/0.62  cnf(c_0_82, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k2_tarski(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_67]), c_0_68]), ['final']).
% 0.46/0.62  cnf(c_0_83, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk4_0)=k2_tarski(esk4_0,esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_69]), c_0_68]), ['final']).
% 0.46/0.62  cnf(c_0_84, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X4|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X3|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X5,X6,k2_tarski(X3,X4))=X5|esk1_3(X5,X6,k2_tarski(X3,X4))=X6|k2_tarski(X3,X4)=k2_tarski(X1,X2)|k2_tarski(X3,X4)=k2_tarski(X5,X6)), inference(spm,[status(thm)],[c_0_71, c_0_10]), ['final']).
% 0.46/0.62  cnf(c_0_85, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X1,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|k2_tarski(X3,X3)=k2_tarski(X1,X2)), inference(ef,[status(thm)],[c_0_72]), ['final']).
% 0.46/0.62  cnf(c_0_86, plain, (k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X3,X4,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|esk1_3(X3,X4,k2_tarski(X2,X2))=X3|esk1_3(X3,X4,k2_tarski(X2,X2))=X4|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X4)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_33]), c_0_27]), ['final']).
% 0.46/0.62  cnf(c_0_87, plain, (k2_tarski(X1,X1)=k2_tarski(X2,X1)|~r2_hidden(X2,k2_tarski(X1,X1))), inference(spm,[status(thm)],[c_0_13, c_0_73]), ['final']).
% 0.46/0.62  cnf(c_0_88, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=X2|k2_tarski(X2,X2)=k2_tarski(X1,X1)|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_17, c_0_28]), ['final']).
% 0.46/0.62  cnf(c_0_89, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X5|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X4|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X3|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5)=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_74, c_0_10]), ['final']).
% 0.46/0.62  cnf(c_0_90, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X3|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_75, c_0_10]), ['final']).
% 0.46/0.62  cnf(c_0_91, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X4)),k2_tarski(X4,X4))=X1|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X4)))=k2_tarski(X4,X4)|esk1_3(X2,X3,k2_tarski(X4,X4))=X3|esk1_3(X2,X3,k2_tarski(X4,X4))=X2|k2_tarski(X4,X4)=k2_tarski(X2,X3)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_76]), c_0_19])]), c_0_27]), ['final']).
% 0.46/0.62  cnf(c_0_92, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X3)),X4,k2_tarski(X3,X3))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),X4)=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|k2_tarski(X3,X3)=k2_tarski(X1,X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_77]), c_0_19])]), c_0_27]), ['final']).
% 0.46/0.62  cnf(c_0_93, plain, (esk1_3(X1,X2,k2_tarski(X2,X3))=X3|k2_tarski(X2,X3)=k2_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X2,X3))), inference(spm,[status(thm)],[c_0_78, c_0_79]), ['final']).
% 0.46/0.62  cnf(c_0_94, plain, (esk1_3(X1,X2,k2_tarski(X1,X3))=X3|k2_tarski(X1,X3)=k2_tarski(X1,X2)|~r2_hidden(X2,k2_tarski(X1,X3))), inference(spm,[status(thm)],[c_0_20, c_0_79]), ['final']).
% 0.46/0.62  cnf(c_0_95, plain, (esk1_3(X1,X2,k2_tarski(X2,X3))=X2|esk1_3(X1,X2,k2_tarski(X2,X3))=X3|esk1_3(X1,X2,k2_tarski(X2,X3))=X1|k2_tarski(X2,X3)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).
% 0.46/0.62  cnf(c_0_96, plain, (esk1_3(X1,X2,k2_tarski(X1,X3))=X1|esk1_3(X1,X2,k2_tarski(X1,X3))=X3|esk1_3(X1,X2,k2_tarski(X1,X3))=X2|k2_tarski(X1,X3)=k2_tarski(X1,X2)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_11])])).
% 0.46/0.62  cnf(c_0_97, plain, (esk1_3(X1,X1,k2_tarski(X2,X1))=X1|esk1_3(X1,X1,k2_tarski(X2,X1))=X2|k2_tarski(X2,X1)=k2_tarski(X1,X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).
% 0.46/0.62  cnf(c_0_98, plain, (esk1_3(X1,X1,k2_tarski(X1,X2))=X1|esk1_3(X1,X1,k2_tarski(X1,X2))=X2|k2_tarski(X1,X2)=k2_tarski(X1,X1)), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).
% 0.46/0.62  cnf(c_0_99, negated_conjecture, (m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k6_domain_1(u1_struct_0(esk2_0),esk3_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_66, c_0_80])).
% 0.46/0.62  cnf(c_0_100, negated_conjecture, (m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k6_domain_1(u1_struct_0(esk2_0),esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_66, c_0_81])).
% 0.46/0.62  cnf(c_0_101, negated_conjecture, (m1_subset_1(k2_tarski(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_80, c_0_82]), ['final']).
% 0.46/0.62  cnf(c_0_102, negated_conjecture, (m1_subset_1(k2_tarski(esk4_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_81, c_0_83]), ['final']).
% 0.46/0.62  cnf(c_0_103, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X3|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X5,X6,k2_tarski(X3,X4))=X6|esk1_3(X5,X6,k2_tarski(X3,X4))=X5|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X5,X6)|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X1,X2,k2_tarski(X3,X4))!=X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_84]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_104, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X3|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X5,X6,k2_tarski(X3,X4))=X6|esk1_3(X5,X6,k2_tarski(X3,X4))=X5|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X5,X6)|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X5,X6,k2_tarski(X3,X4))!=X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_84]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_105, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X5,X6,k2_tarski(X3,X4))=X6|esk1_3(X5,X6,k2_tarski(X3,X4))=X5|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X5,X6)|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X1,X2,k2_tarski(X3,X4))!=X3), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_84]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_106, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X5,X6,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X5,X6,k2_tarski(X3,X4))=X6|esk1_3(X5,X6,k2_tarski(X3,X4))=X5|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X5,X6)|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X5,X6,k2_tarski(X3,X4))!=X3), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_84]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_107, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|X4=esk1_3(X1,X2,k2_tarski(X3,X3))|k2_tarski(X3,X3)=k2_tarski(X1,X2)|~r2_hidden(X4,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_9, c_0_85]), ['final']).
% 0.46/0.62  cnf(c_0_108, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=X1|X3=esk1_3(X1,X1,k2_tarski(X2,X2))|k2_tarski(X2,X2)=k2_tarski(X1,X1)|~r2_hidden(X3,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_9, c_0_41]), ['final']).
% 0.46/0.62  cnf(c_0_109, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),esk1_3(X4,X4,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|esk1_3(X4,X4,k2_tarski(X3,X3))=X4|k2_tarski(X3,X3)=k2_tarski(X1,X2)|k2_tarski(X3,X3)=k2_tarski(X4,X4)), inference(spm,[status(thm)],[c_0_33, c_0_29]), ['final']).
% 0.46/0.62  cnf(c_0_110, plain, (k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),esk1_3(X3,X3,k2_tarski(X2,X2)))=k2_tarski(X2,X2)|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|esk1_3(X3,X3,k2_tarski(X2,X2))=X3|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X3)), inference(spm,[status(thm)],[c_0_33, c_0_86]), ['final']).
% 0.46/0.62  cnf(c_0_111, plain, (esk1_3(X1,esk1_3(X2,X2,k2_tarski(X3,X3)),k2_tarski(X3,X3))=X1|k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X2,X2,k2_tarski(X3,X3))=X2|k2_tarski(X3,X3)=k2_tarski(X2,X2)), inference(spm,[status(thm)],[c_0_73, c_0_86]), ['final']).
% 0.46/0.62  cnf(c_0_112, plain, (esk1_3(esk1_3(X1,X1,k2_tarski(X2,X2)),X3,k2_tarski(X2,X2))=X3|k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),X3)=k2_tarski(X2,X2)|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_21, c_0_86]), ['final']).
% 0.46/0.62  cnf(c_0_113, plain, (k2_tarski(X1,esk1_3(X2,X2,k2_tarski(X3,X3)))=k2_tarski(X3,X3)|esk1_3(X2,X2,k2_tarski(X3,X3))=X2|k2_tarski(X3,X3)=k2_tarski(X2,X2)|~r2_hidden(X1,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_87, c_0_86]), ['final']).
% 0.46/0.62  cnf(c_0_114, plain, (k2_tarski(esk1_3(X1,X1,k2_tarski(X2,X2)),X3)=k2_tarski(X2,X2)|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|k2_tarski(X2,X2)=k2_tarski(X1,X1)|~r2_hidden(X3,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_23, c_0_86]), ['final']).
% 0.46/0.62  cnf(c_0_115, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(X3,X4,k2_tarski(X2,X2))|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|esk1_3(X3,X4,k2_tarski(X2,X2))=X4|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X4)|~r2_hidden(X3,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_13, c_0_30]), ['final']).
% 0.46/0.62  cnf(c_0_116, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(X3,X4,k2_tarski(X2,X2))|esk1_3(X1,X1,k2_tarski(X2,X2))=X1|esk1_3(X3,X4,k2_tarski(X2,X2))=X3|k2_tarski(X2,X2)=k2_tarski(X1,X1)|k2_tarski(X2,X2)=k2_tarski(X3,X4)|~r2_hidden(X4,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_17, c_0_30]), ['final']).
% 0.46/0.62  cnf(c_0_117, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=esk1_3(X4,X5,k2_tarski(X3,X3))|esk1_3(X4,X5,k2_tarski(X3,X3))=X4|esk1_3(X4,X5,k2_tarski(X3,X3))=X5|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|k2_tarski(X3,X3)=k2_tarski(X4,X5)|k2_tarski(X3,X3)=k2_tarski(X1,X2)|~r2_hidden(X2,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_63, c_0_29]), ['final']).
% 0.46/0.62  cnf(c_0_118, plain, (esk1_3(X1,X2,k2_tarski(X3,X3))=esk1_3(X4,X5,k2_tarski(X3,X3))|esk1_3(X4,X5,k2_tarski(X3,X3))=X4|esk1_3(X4,X5,k2_tarski(X3,X3))=X5|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|k2_tarski(X3,X3)=k2_tarski(X4,X5)|k2_tarski(X3,X3)=k2_tarski(X1,X2)|~r2_hidden(X1,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_64, c_0_29]), ['final']).
% 0.46/0.62  cnf(c_0_119, plain, (esk1_3(X1,X1,k2_tarski(X2,X2))=esk1_3(X3,X4,k2_tarski(X2,X2))|esk1_3(X3,X4,k2_tarski(X2,X2))=X3|esk1_3(X3,X4,k2_tarski(X2,X2))=X4|k2_tarski(X2,X2)=k2_tarski(X3,X4)|k2_tarski(X2,X2)=k2_tarski(X1,X1)|~r2_hidden(X1,k2_tarski(X2,X2))), inference(spm,[status(thm)],[c_0_88, c_0_29]), ['final']).
% 0.46/0.62  cnf(c_0_120, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X3|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X5|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5)=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X1,X2,k2_tarski(X3,X4))!=X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_89]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_121, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X4|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X5|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5)=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X1,X2,k2_tarski(X3,X4))!=X3), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_89]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_122, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X4|esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X1|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5)))=k2_tarski(X4,X5)|esk1_3(X2,X3,k2_tarski(X4,X5))=X3|esk1_3(X2,X3,k2_tarski(X4,X5))=X2|k2_tarski(X4,X5)=k2_tarski(X2,X3)|esk1_3(X2,X3,k2_tarski(X4,X5))!=X5), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_60]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_123, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X5|esk1_3(X1,esk1_3(X2,X3,k2_tarski(X4,X5)),k2_tarski(X4,X5))=X1|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X5)))=k2_tarski(X4,X5)|esk1_3(X2,X3,k2_tarski(X4,X5))=X3|esk1_3(X2,X3,k2_tarski(X4,X5))=X2|k2_tarski(X4,X5)=k2_tarski(X2,X3)|esk1_3(X2,X3,k2_tarski(X4,X5))!=X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_60]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_124, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X3|esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X5,k2_tarski(X3,X4))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),X5)=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X1,X2)|~r2_hidden(X5,k2_tarski(X3,X4))), inference(spm,[status(thm)],[c_0_17, c_0_89]), ['final']).
% 0.46/0.62  cnf(c_0_125, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X4|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X1,X2,k2_tarski(X3,X4))!=X3), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_90]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_126, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)),k2_tarski(X3,X4))=X3|k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X4)),esk1_3(X1,X2,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|k2_tarski(X3,X4)=k2_tarski(X1,X2)|esk1_3(X1,X2,k2_tarski(X3,X4))!=X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_90]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_127, plain, (k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X4,X4)))=k2_tarski(X4,X4)|esk1_3(X2,X3,k2_tarski(X4,X4))=X2|esk1_3(X2,X3,k2_tarski(X4,X4))=X3|k2_tarski(X4,X4)=k2_tarski(X2,X3)|~r2_hidden(X1,k2_tarski(X4,X4))), inference(spm,[status(thm)],[c_0_13, c_0_91]), ['final']).
% 0.46/0.62  cnf(c_0_128, plain, (k2_tarski(esk1_3(X1,X2,k2_tarski(X3,X3)),X4)=k2_tarski(X3,X3)|esk1_3(X1,X2,k2_tarski(X3,X3))=X1|esk1_3(X1,X2,k2_tarski(X3,X3))=X2|k2_tarski(X3,X3)=k2_tarski(X1,X2)|~r2_hidden(X4,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_17, c_0_92]), ['final']).
% 0.46/0.62  cnf(c_0_129, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X3,k2_tarski(X3,X4))=X4|k2_tarski(X3,esk1_3(X1,X2,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_10]), c_0_79]), ['final']).
% 0.46/0.62  cnf(c_0_130, plain, (esk1_3(esk1_3(X1,X2,k2_tarski(X3,X4)),X4,k2_tarski(X3,X4))=X3|k2_tarski(X4,esk1_3(X1,X2,k2_tarski(X3,X4)))=k2_tarski(X3,X4)|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_10]), c_0_79]), ['final']).
% 0.46/0.62  cnf(c_0_131, plain, (esk1_3(X1,esk1_3(X2,X3,k2_tarski(X1,X4)),k2_tarski(X1,X4))=X4|k2_tarski(X1,esk1_3(X2,X3,k2_tarski(X1,X4)))=k2_tarski(X1,X4)|esk1_3(X2,X3,k2_tarski(X1,X4))=X2|esk1_3(X2,X3,k2_tarski(X1,X4))=X3|k2_tarski(X1,X4)=k2_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_94, c_0_10]), ['final']).
% 0.46/0.62  cnf(c_0_132, plain, (esk1_3(X1,X2,k2_tarski(X2,X3))=X1|esk1_3(X1,X2,k2_tarski(X2,X3))=X3|k2_tarski(X2,X3)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_95]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_133, plain, (esk1_3(X1,X2,k2_tarski(X1,X3))=X2|esk1_3(X1,X2,k2_tarski(X1,X3))=X3|k2_tarski(X1,X3)=k2_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_96]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_134, plain, (esk1_3(X1,X1,k2_tarski(X2,X1))=X2|k2_tarski(X2,X1)=k2_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_97]), c_0_15])]), ['final']).
% 0.46/0.62  cnf(c_0_135, plain, (esk1_3(X1,X1,k2_tarski(X1,X2))=X2|k2_tarski(X1,X2)=k2_tarski(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_98]), c_0_19])]), ['final']).
% 0.46/0.62  cnf(c_0_136, negated_conjecture, (m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk3_0,esk3_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_99, c_0_82]), ['final']).
% 0.46/0.62  cnf(c_0_137, negated_conjecture, (m1_subset_1(k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk4_0,esk4_0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(rw,[status(thm)],[c_0_100, c_0_83]), ['final']).
% 0.46/0.62  cnf(c_0_138, negated_conjecture, (k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk3_0,esk3_0))=k2_tarski(k2_tarski(esk3_0,esk3_0),k2_tarski(esk3_0,esk3_0))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_70, c_0_101]), ['final']).
% 0.46/0.62  cnf(c_0_139, negated_conjecture, (k6_domain_1(k1_zfmisc_1(u1_struct_0(esk2_0)),k2_tarski(esk4_0,esk4_0))=k2_tarski(k2_tarski(esk4_0,esk4_0),k2_tarski(esk4_0,esk4_0))|v1_xboole_0(k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_70, c_0_102]), ['final']).
% 0.46/0.62  cnf(c_0_140, negated_conjecture, (r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))|r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.46/0.62  cnf(c_0_141, negated_conjecture, (~r2_hidden(esk4_0,k6_waybel_0(esk2_0,esk3_0))|~r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_44]), ['final']).
% 0.46/0.62  # SZS output end Saturation
% 0.46/0.62  # Proof object total steps             : 142
% 0.46/0.62  # Proof object clause steps            : 127
% 0.46/0.62  # Proof object formula steps           : 15
% 0.46/0.62  # Proof object conjectures             : 23
% 0.46/0.62  # Proof object clause conjectures      : 20
% 0.46/0.62  # Proof object formula conjectures     : 3
% 0.46/0.62  # Proof object initial clauses used    : 17
% 0.46/0.62  # Proof object initial formulas used   : 7
% 0.46/0.62  # Proof object generating inferences   : 102
% 0.46/0.62  # Proof object simplifying inferences  : 82
% 0.46/0.62  # Parsed axioms                        : 7
% 0.46/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.62  # Initial clauses                      : 17
% 0.46/0.62  # Removed in clause preprocessing      : 1
% 0.46/0.62  # Initial clauses in saturation        : 16
% 0.46/0.62  # Processed clauses                    : 2478
% 0.46/0.62  # ...of these trivial                  : 68
% 0.46/0.62  # ...subsumed                          : 2242
% 0.46/0.62  # ...remaining for further processing  : 168
% 0.46/0.62  # Other redundant clauses eliminated   : 325
% 0.46/0.62  # Clauses deleted for lack of memory   : 0
% 0.46/0.62  # Backward-subsumed                    : 45
% 0.46/0.62  # Backward-rewritten                   : 4
% 0.46/0.62  # Generated clauses                    : 4591
% 0.46/0.62  # ...of the previous two non-trivial   : 4088
% 0.46/0.62  # Contextual simplify-reflections      : 7
% 0.46/0.62  # Paramodulations                      : 4141
% 0.46/0.62  # Factorizations                       : 127
% 0.46/0.62  # Equation resolutions                 : 325
% 0.46/0.62  # Propositional unsat checks           : 0
% 0.46/0.62  #    Propositional check models        : 0
% 0.46/0.62  #    Propositional check unsatisfiable : 0
% 0.46/0.62  #    Propositional clauses             : 0
% 0.46/0.62  #    Propositional clauses after purity: 0
% 0.46/0.62  #    Propositional unsat core size     : 0
% 0.46/0.62  #    Propositional preprocessing time  : 0.000
% 0.46/0.62  #    Propositional encoding time       : 0.000
% 0.46/0.62  #    Propositional solver time         : 0.000
% 0.46/0.62  #    Success case prop preproc time    : 0.000
% 0.46/0.62  #    Success case prop encoding time   : 0.000
% 0.46/0.62  #    Success case prop solver time     : 0.000
% 0.46/0.62  # Current number of processed clauses  : 100
% 0.46/0.62  #    Positive orientable unit clauses  : 10
% 0.46/0.62  #    Positive unorientable unit clauses: 1
% 0.46/0.62  #    Negative unit clauses             : 2
% 0.46/0.62  #    Non-unit-clauses                  : 87
% 0.46/0.62  # Current number of unprocessed clauses: 0
% 0.46/0.62  # ...number of literals in the above   : 0
% 0.46/0.62  # Current number of archived formulas  : 0
% 0.46/0.62  # Current number of archived clauses   : 66
% 0.46/0.62  # Clause-clause subsumption calls (NU) : 60824
% 0.46/0.62  # Rec. Clause-clause subsumption calls : 5497
% 0.46/0.62  # Non-unit clause-clause subsumptions  : 2293
% 0.46/0.62  # Unit Clause-clause subsumption calls : 19
% 0.46/0.62  # Rewrite failures with RHS unbound    : 0
% 0.46/0.62  # BW rewrite match attempts            : 28
% 0.46/0.62  # BW rewrite match successes           : 26
% 0.46/0.62  # Condensation attempts                : 0
% 0.46/0.62  # Condensation successes               : 0
% 0.46/0.62  # Termbank termtop insertions          : 128671
% 0.46/0.62  
% 0.46/0.62  # -------------------------------------------------
% 0.46/0.62  # User time                : 0.269 s
% 0.46/0.62  # System time              : 0.009 s
% 0.46/0.62  # Total time               : 0.278 s
% 0.46/0.62  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
