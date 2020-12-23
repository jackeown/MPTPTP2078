%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:25 EST 2020

% Result     : CounterSatisfiable 0.17s
% Output     : Saturation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 109 expanded)
%              Number of clauses        :   32 (  36 expanded)
%              Number of leaves         :    8 (  29 expanded)
%              Depth                    :    4
%              Number of atoms          :  234 ( 897 expanded)
%              Number of equality atoms :   15 (  76 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v15_waybel_0(X2,X1)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & X2 = k6_waybel_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_waybel_0)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v15_waybel_0(X2,X1)
            <=> ? [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                  & X2 = k6_waybel_0(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_waybel_0])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( m1_subset_1(esk1_3(X7,X8,X9),X7)
        | r1_tarski(X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r1_tarski(X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) )
      & ( ~ r2_hidden(esk1_3(X7,X8,X9),X9)
        | r1_tarski(X8,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X29] :
      ( ~ v2_struct_0(esk3_0)
      & v3_orders_2(esk3_0)
      & v4_orders_2(esk3_0)
      & l1_orders_2(esk3_0)
      & ~ v1_xboole_0(esk4_0)
      & v2_waybel_0(esk4_0,esk3_0)
      & v13_waybel_0(esk4_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & ( ~ v15_waybel_0(esk4_0,esk3_0)
        | ~ m1_subset_1(X29,u1_struct_0(esk3_0))
        | esk4_0 != k6_waybel_0(esk3_0,X29) )
      & ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
        | v15_waybel_0(esk4_0,esk3_0) )
      & ( esk4_0 = k6_waybel_0(esk3_0,esk5_0)
        | v15_waybel_0(esk4_0,esk3_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).

fof(c_0_11,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_12,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_16,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( ~ v15_waybel_0(esk4_0,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | esk4_0 != k6_waybel_0(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    | v15_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( esk4_0 = k6_waybel_0(esk3_0,esk5_0)
    | v15_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

fof(c_0_21,plain,(
    ! [X14,X15,X16] :
      ( ( ~ r3_orders_2(X14,X15,X16)
        | r1_orders_2(X14,X15,X16)
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ l1_orders_2(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ m1_subset_1(X16,u1_struct_0(X14)) )
      & ( ~ r1_orders_2(X14,X15,X16)
        | r3_orders_2(X14,X15,X16)
        | v2_struct_0(X14)
        | ~ v3_orders_2(X14)
        | ~ l1_orders_2(X14)
        | ~ m1_subset_1(X15,u1_struct_0(X14))
        | ~ m1_subset_1(X16,u1_struct_0(X14)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_22,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ r2_hidden(X25,X23)
        | r1_orders_2(X22,X24,X25)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) )
      & ( ~ r1_orders_2(X22,X24,esk2_3(X22,X23,X24))
        | r1_lattice3(X22,X23,X24)
        | ~ m1_subset_1(X24,u1_struct_0(X22))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | r3_orders_2(X17,X18,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

fof(c_0_24,plain,(
    ! [X20,X21] :
      ( v2_struct_0(X20)
      | ~ v3_orders_2(X20)
      | ~ l1_orders_2(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | r1_orders_2(X20,X21,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_3(u1_struct_0(esk3_0),X1,esk4_0),X1)
    | r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1_3(u1_struct_0(esk3_0),X1,esk4_0),u1_struct_0(esk3_0))
    | r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_14]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,esk4_0)
    | ~ r2_hidden(esk1_3(u1_struct_0(esk3_0),X1,esk4_0),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    | k6_waybel_0(esk3_0,X1) != esk4_0
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( k6_waybel_0(esk3_0,esk5_0) = esk4_0
    | k6_waybel_0(esk3_0,X1) != esk4_0
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_20]),
    [final]).

cnf(c_0_32,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_33,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_34,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_35,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

cnf(c_0_36,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_37,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24]),
    [final]).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_25]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( v13_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( v2_waybel_0(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n025.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:38:21 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.17/0.36  # and selection function SelectNewComplexAHP.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.030 s
% 0.17/0.36  # Presaturation interreduction done
% 0.17/0.36  
% 0.17/0.36  # No proof found!
% 0.17/0.36  # SZS status CounterSatisfiable
% 0.17/0.36  # SZS output start Saturation
% 0.17/0.36  fof(t49_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v15_waybel_0(X2,X1)<=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&X2=k6_waybel_0(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_waybel_0)).
% 0.17/0.36  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.17/0.36  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.17/0.36  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.17/0.36  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.17/0.36  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.17/0.36  fof(reflexivity_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>r3_orders_2(X1,X2,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 0.17/0.36  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.17/0.36  fof(c_0_8, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v15_waybel_0(X2,X1)<=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&X2=k6_waybel_0(X1,X3)))))), inference(assume_negation,[status(cth)],[t49_waybel_0])).
% 0.17/0.36  fof(c_0_9, plain, ![X7, X8, X9]:((m1_subset_1(esk1_3(X7,X8,X9),X7)|r1_tarski(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X7))|~m1_subset_1(X8,k1_zfmisc_1(X7)))&((r2_hidden(esk1_3(X7,X8,X9),X8)|r1_tarski(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X7))|~m1_subset_1(X8,k1_zfmisc_1(X7)))&(~r2_hidden(esk1_3(X7,X8,X9),X9)|r1_tarski(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X7))|~m1_subset_1(X8,k1_zfmisc_1(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.17/0.36  fof(c_0_10, negated_conjecture, ![X29]:((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&l1_orders_2(esk3_0))&((((~v1_xboole_0(esk4_0)&v2_waybel_0(esk4_0,esk3_0))&v13_waybel_0(esk4_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))))&((~v15_waybel_0(esk4_0,esk3_0)|(~m1_subset_1(X29,u1_struct_0(esk3_0))|esk4_0!=k6_waybel_0(esk3_0,X29)))&((m1_subset_1(esk5_0,u1_struct_0(esk3_0))|v15_waybel_0(esk4_0,esk3_0))&(esk4_0=k6_waybel_0(esk3_0,esk5_0)|v15_waybel_0(esk4_0,esk3_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])])).
% 0.17/0.36  fof(c_0_11, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.17/0.36  fof(c_0_12, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.17/0.36  cnf(c_0_13, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.17/0.36  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_15, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.17/0.36  cnf(c_0_16, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.17/0.36  cnf(c_0_17, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_11]), ['final']).
% 0.17/0.36  cnf(c_0_18, negated_conjecture, (~v15_waybel_0(esk4_0,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk3_0))|esk4_0!=k6_waybel_0(esk3_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))|v15_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_20, negated_conjecture, (esk4_0=k6_waybel_0(esk3_0,esk5_0)|v15_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  fof(c_0_21, plain, ![X14, X15, X16]:((~r3_orders_2(X14,X15,X16)|r1_orders_2(X14,X15,X16)|(v2_struct_0(X14)|~v3_orders_2(X14)|~l1_orders_2(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))))&(~r1_orders_2(X14,X15,X16)|r3_orders_2(X14,X15,X16)|(v2_struct_0(X14)|~v3_orders_2(X14)|~l1_orders_2(X14)|~m1_subset_1(X15,u1_struct_0(X14))|~m1_subset_1(X16,u1_struct_0(X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.17/0.36  fof(c_0_22, plain, ![X22, X23, X24, X25]:((~r1_lattice3(X22,X23,X24)|(~m1_subset_1(X25,u1_struct_0(X22))|(~r2_hidden(X25,X23)|r1_orders_2(X22,X24,X25)))|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((m1_subset_1(esk2_3(X22,X23,X24),u1_struct_0(X22))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&((r2_hidden(esk2_3(X22,X23,X24),X23)|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))&(~r1_orders_2(X22,X24,esk2_3(X22,X23,X24))|r1_lattice3(X22,X23,X24)|~m1_subset_1(X24,u1_struct_0(X22))|~l1_orders_2(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.17/0.36  fof(c_0_23, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|~m1_subset_1(X18,u1_struct_0(X17))|~m1_subset_1(X19,u1_struct_0(X17))|r3_orders_2(X17,X18,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).
% 0.17/0.36  fof(c_0_24, plain, ![X20, X21]:(v2_struct_0(X20)|~v3_orders_2(X20)|~l1_orders_2(X20)|(~m1_subset_1(X21,u1_struct_0(X20))|r1_orders_2(X20,X21,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.17/0.36  cnf(c_0_25, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.36  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_3(u1_struct_0(esk3_0),X1,esk4_0),X1)|r1_tarski(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.17/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk1_3(u1_struct_0(esk3_0),X1,esk4_0),u1_struct_0(esk3_0))|r1_tarski(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_15, c_0_14]), ['final']).
% 0.17/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,esk4_0)|~r2_hidden(esk1_3(u1_struct_0(esk3_0),X1,esk4_0),esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_16, c_0_14]), ['final']).
% 0.17/0.36  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_17, c_0_14]), ['final']).
% 0.17/0.36  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))|k6_waybel_0(esk3_0,X1)!=esk4_0|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.17/0.36  cnf(c_0_31, negated_conjecture, (k6_waybel_0(esk3_0,esk5_0)=esk4_0|k6_waybel_0(esk3_0,X1)!=esk4_0|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_20]), ['final']).
% 0.17/0.36  cnf(c_0_32, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.17/0.36  cnf(c_0_33, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.17/0.36  cnf(c_0_34, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.17/0.36  cnf(c_0_35, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.17/0.36  cnf(c_0_36, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.17/0.36  cnf(c_0_37, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.17/0.36  cnf(c_0_38, plain, (v2_struct_0(X1)|r3_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.17/0.36  cnf(c_0_39, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24]), ['final']).
% 0.17/0.36  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.17/0.36  cnf(c_0_41, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_43, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_25]), ['final']).
% 0.17/0.36  cnf(c_0_44, negated_conjecture, (v13_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_45, negated_conjecture, (v2_waybel_0(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_46, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  cnf(c_0_48, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.17/0.36  # SZS output end Saturation
% 0.17/0.36  # Proof object total steps             : 49
% 0.17/0.36  # Proof object clause steps            : 32
% 0.17/0.36  # Proof object formula steps           : 17
% 0.17/0.36  # Proof object conjectures             : 20
% 0.17/0.36  # Proof object clause conjectures      : 17
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 25
% 0.17/0.36  # Proof object initial formulas used   : 8
% 0.17/0.36  # Proof object generating inferences   : 6
% 0.17/0.36  # Proof object simplifying inferences  : 1
% 0.17/0.36  # Parsed axioms                        : 8
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 26
% 0.17/0.36  # Removed in clause preprocessing      : 0
% 0.17/0.36  # Initial clauses in saturation        : 26
% 0.17/0.36  # Processed clauses                    : 59
% 0.17/0.36  # ...of these trivial                  : 1
% 0.17/0.36  # ...subsumed                          : 0
% 0.17/0.36  # ...remaining for further processing  : 58
% 0.17/0.36  # Other redundant clauses eliminated   : 2
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 0
% 0.17/0.36  # Backward-rewritten                   : 0
% 0.17/0.36  # Generated clauses                    : 11
% 0.17/0.36  # ...of the previous two non-trivial   : 8
% 0.17/0.36  # Contextual simplify-reflections      : 0
% 0.17/0.36  # Paramodulations                      : 9
% 0.17/0.36  # Factorizations                       : 0
% 0.17/0.36  # Equation resolutions                 : 2
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 31
% 0.17/0.36  #    Positive orientable unit clauses  : 7
% 0.17/0.36  #    Positive unorientable unit clauses: 0
% 0.17/0.36  #    Negative unit clauses             : 2
% 0.17/0.36  #    Non-unit-clauses                  : 22
% 0.17/0.36  # Current number of unprocessed clauses: 0
% 0.17/0.36  # ...number of literals in the above   : 0
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 25
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 39
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 7
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 0
% 0.17/0.36  # Unit Clause-clause subsumption calls : 3
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 3
% 0.17/0.36  # BW rewrite match successes           : 0
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 2615
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.034 s
% 0.17/0.36  # System time              : 0.003 s
% 0.17/0.36  # Total time               : 0.036 s
% 0.17/0.36  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
