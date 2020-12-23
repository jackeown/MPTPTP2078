%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:17 EST 2020

% Result     : CounterSatisfiable 0.14s
% Output     : Saturation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 243 expanded)
%              Number of clauses        :   43 (  95 expanded)
%              Number of leaves         :    7 (  64 expanded)
%              Depth                    :    6
%              Number of atoms          :  185 (1246 expanded)
%              Number of equality atoms :   38 ( 251 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t24_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( X2 = k13_lattice3(X1,X2,X3)
              <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_7,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X10,X9)
        | r2_hidden(X10,X9)
        | v1_xboole_0(X9) )
      & ( ~ r2_hidden(X10,X9)
        | m1_subset_1(X10,X9)
        | v1_xboole_0(X9) )
      & ( ~ m1_subset_1(X10,X9)
        | v1_xboole_0(X10)
        | ~ v1_xboole_0(X9) )
      & ( ~ v1_xboole_0(X10)
        | m1_subset_1(X10,X9)
        | ~ v1_xboole_0(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( X2 = k13_lattice3(X1,X2,X3)
                <=> r1_orders_2(X1,X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_0])).

fof(c_0_12,plain,(
    ! [X11,X13,X14] :
      ( ( r2_hidden(esk2_1(X11),X11)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(X13,X11)
        | esk2_1(X11) != k4_tarski(X13,X14)
        | X11 = k1_xboole_0 )
      & ( ~ r2_hidden(X14,X11)
        | esk2_1(X11) != k4_tarski(X13,X14)
        | X11 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v3_orders_2(X17)
      | ~ l1_orders_2(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | r1_orders_2(X17,X18,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

fof(c_0_16,negated_conjecture,
    ( v3_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & v1_lattice3(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & ( esk4_0 != k13_lattice3(esk3_0,esk4_0,esk5_0)
      | ~ r1_orders_2(esk3_0,esk5_0,esk4_0) )
    & ( esk4_0 = k13_lattice3(esk3_0,esk4_0,esk5_0)
      | r1_orders_2(esk3_0,esk5_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_18,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15]),
    [final]).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_23,plain,
    ( X1 = k1_xboole_0
    | m1_subset_1(esk2_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_25,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k4_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_17]),
    [final]).

cnf(c_0_27,plain,
    ( r1_orders_2(X1,esk1_1(u1_struct_0(X1)),esk1_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_30,plain,
    ( X2 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | esk2_1(X2) != k4_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22]),
    [final]).

cnf(c_0_33,plain,
    ( u1_struct_0(X1) = k1_xboole_0
    | r1_orders_2(X1,esk2_1(u1_struct_0(X1)),esk2_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_23]),
    [final]).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

fof(c_0_35,plain,(
    ! [X15] :
      ( ~ v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | v1_xboole_0(u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_36,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_37,plain,
    ( r1_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_24]),
    [final]).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk1_1(X1),X2) != esk2_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_15]),c_0_26]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( r1_orders_2(esk3_0,esk1_1(u1_struct_0(esk3_0)),esk1_1(u1_struct_0(esk3_0)))
    | v2_struct_0(esk3_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [final]).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(esk2_1(X1),X2) != esk2_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17]),
    [final]).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk1_1(X1)) != esk2_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_15]),c_0_26]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk2_1(u1_struct_0(esk3_0)) != k4_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_31]),c_0_26]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk2_1(u1_struct_0(esk3_0)) != k4_tarski(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_32]),c_0_26]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r1_orders_2(esk3_0,esk4_0,esk4_0)
    | v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_21]),c_0_28]),c_0_29])]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r1_orders_2(esk3_0,esk5_0,esk5_0)
    | v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_22]),c_0_28]),c_0_29])]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | r1_orders_2(esk3_0,esk2_1(u1_struct_0(esk3_0)),esk2_1(u1_struct_0(esk3_0)))
    | v2_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])]),
    [final]).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | k4_tarski(X2,esk2_1(X1)) != esk2_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_17]),
    [final]).

cnf(c_0_48,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk2_1(u1_struct_0(esk3_0)) != k4_tarski(X1,esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_26]),
    [final]).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0
    | esk2_1(u1_struct_0(esk3_0)) != k4_tarski(X1,esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_32]),c_0_26]),
    [final]).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21]),
    [final]).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_22]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( esk4_0 != k13_lattice3(esk3_0,esk4_0,esk5_0)
    | ~ r1_orders_2(esk3_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_53,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = k13_lattice3(esk3_0,esk4_0,esk5_0)
    | r1_orders_2(esk3_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_55,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( v1_lattice3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # No proof found!
% 0.14/0.38  # SZS status CounterSatisfiable
% 0.14/0.38  # SZS output start Saturation
% 0.14/0.38  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 0.14/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.38  fof(t24_yellow_0, conjecture, ![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_0)).
% 0.14/0.38  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.14/0.38  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.14/0.38  fof(fc1_struct_0, axiom, ![X1]:((v2_struct_0(X1)&l1_struct_0(X1))=>v1_xboole_0(u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 0.14/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.14/0.38  fof(c_0_7, plain, ![X9, X10]:(((~m1_subset_1(X10,X9)|r2_hidden(X10,X9)|v1_xboole_0(X9))&(~r2_hidden(X10,X9)|m1_subset_1(X10,X9)|v1_xboole_0(X9)))&((~m1_subset_1(X10,X9)|v1_xboole_0(X10)|~v1_xboole_0(X9))&(~v1_xboole_0(X10)|m1_subset_1(X10,X9)|~v1_xboole_0(X9)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.14/0.38  fof(c_0_8, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.38  cnf(c_0_9, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_10, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(X2=k13_lattice3(X1,X2,X3)<=>r1_orders_2(X1,X3,X2)))))), inference(assume_negation,[status(cth)],[t24_yellow_0])).
% 0.14/0.38  fof(c_0_12, plain, ![X11, X13, X14]:((r2_hidden(esk2_1(X11),X11)|X11=k1_xboole_0)&((~r2_hidden(X13,X11)|esk2_1(X11)!=k4_tarski(X13,X14)|X11=k1_xboole_0)&(~r2_hidden(X14,X11)|esk2_1(X11)!=k4_tarski(X13,X14)|X11=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X17, X18]:(v2_struct_0(X17)|~v3_orders_2(X17)|~l1_orders_2(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|r1_orders_2(X17,X18,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.14/0.38  cnf(c_0_14, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.14/0.38  fof(c_0_16, negated_conjecture, ((((v3_orders_2(esk3_0)&v5_orders_2(esk3_0))&v1_lattice3(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&((esk4_0!=k13_lattice3(esk3_0,esk4_0,esk5_0)|~r1_orders_2(esk3_0,esk5_0,esk4_0))&(esk4_0=k13_lattice3(esk3_0,esk4_0,esk5_0)|r1_orders_2(esk3_0,esk5_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.14/0.38  cnf(c_0_17, plain, (r2_hidden(esk2_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_18, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_13]), ['final']).
% 0.14/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15]), ['final']).
% 0.14/0.38  cnf(c_0_20, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_23, plain, (X1=k1_xboole_0|m1_subset_1(esk2_1(X1),X1)), inference(spm,[status(thm)],[c_0_14, c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_24, plain, (m1_subset_1(X1,X2)|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  cnf(c_0_25, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k4_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_26, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_10, c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_27, plain, (r1_orders_2(X1,esk1_1(u1_struct_0(X1)),esk1_1(u1_struct_0(X1)))|v2_struct_0(X1)|v1_xboole_0(u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_30, plain, (X2=k1_xboole_0|~r2_hidden(X1,X2)|esk2_1(X2)!=k4_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12]), ['final']).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_21]), ['final']).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_33, plain, (u1_struct_0(X1)=k1_xboole_0|r1_orders_2(X1,esk2_1(u1_struct_0(X1)),esk2_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_23]), ['final']).
% 0.14/0.38  cnf(c_0_34, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.14/0.38  fof(c_0_35, plain, ![X15]:(~v2_struct_0(X15)|~l1_struct_0(X15)|v1_xboole_0(u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).
% 0.14/0.38  fof(c_0_36, plain, ![X16]:(~l1_orders_2(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.14/0.38  cnf(c_0_37, plain, (r1_orders_2(X1,X2,X2)|v2_struct_0(X1)|~v3_orders_2(X1)|~l1_orders_2(X1)|~v1_xboole_0(u1_struct_0(X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_18, c_0_24]), ['final']).
% 0.14/0.38  cnf(c_0_38, plain, (X1=k1_xboole_0|k4_tarski(esk1_1(X1),X2)!=esk2_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_15]), c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (r1_orders_2(esk3_0,esk1_1(u1_struct_0(esk3_0)),esk1_1(u1_struct_0(esk3_0)))|v2_struct_0(esk3_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), ['final']).
% 0.14/0.38  cnf(c_0_40, plain, (X1=k1_xboole_0|k4_tarski(esk2_1(X1),X2)!=esk2_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_41, plain, (X1=k1_xboole_0|k4_tarski(X2,esk1_1(X1))!=esk2_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_15]), c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk2_1(u1_struct_0(esk3_0))!=k4_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_31]), c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk2_1(u1_struct_0(esk3_0))!=k4_tarski(esk5_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_32]), c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, (r1_orders_2(esk3_0,esk4_0,esk4_0)|v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_21]), c_0_28]), c_0_29])]), ['final']).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (r1_orders_2(esk3_0,esk5_0,esk5_0)|v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_22]), c_0_28]), c_0_29])]), ['final']).
% 0.14/0.38  cnf(c_0_46, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|r1_orders_2(esk3_0,esk2_1(u1_struct_0(esk3_0)),esk2_1(u1_struct_0(esk3_0)))|v2_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_28]), c_0_29])]), ['final']).
% 0.14/0.38  cnf(c_0_47, plain, (X1=k1_xboole_0|k4_tarski(X2,esk2_1(X1))!=esk2_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_17]), ['final']).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk2_1(u1_struct_0(esk3_0))!=k4_tarski(X1,esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0|esk2_1(u1_struct_0(esk3_0))!=k4_tarski(X1,esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_32]), c_0_26]), ['final']).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_21]), ['final']).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_34, c_0_22]), ['final']).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (esk4_0!=k13_lattice3(esk3_0,esk4_0,esk5_0)|~r1_orders_2(esk3_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_53, plain, (v1_xboole_0(u1_struct_0(X1))|~v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_35]), ['final']).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (esk4_0=k13_lattice3(esk3_0,esk4_0,esk5_0)|r1_orders_2(esk3_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_55, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_36]), ['final']).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (v1_lattice3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.14/0.38  # SZS output end Saturation
% 0.14/0.38  # Proof object total steps             : 58
% 0.14/0.38  # Proof object clause steps            : 43
% 0.14/0.38  # Proof object formula steps           : 15
% 0.14/0.38  # Proof object conjectures             : 23
% 0.14/0.38  # Proof object clause conjectures      : 20
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 20
% 0.14/0.38  # Proof object initial formulas used   : 7
% 0.14/0.38  # Proof object generating inferences   : 22
% 0.14/0.38  # Proof object simplifying inferences  : 17
% 0.14/0.38  # Parsed axioms                        : 7
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 20
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 65
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 3
% 0.14/0.38  # ...remaining for further processing  : 62
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 0
% 0.14/0.38  # Generated clauses                    : 34
% 0.14/0.38  # ...of the previous two non-trivial   : 25
% 0.14/0.38  # Contextual simplify-reflections      : 7
% 0.14/0.38  # Paramodulations                      : 34
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 42
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 36
% 0.14/0.38  # Current number of unprocessed clauses: 0
% 0.14/0.38  # ...number of literals in the above   : 0
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 20
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 113
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 54
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.14/0.38  # Unit Clause-clause subsumption calls : 0
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 0
% 0.14/0.38  # BW rewrite match successes           : 0
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1807
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
