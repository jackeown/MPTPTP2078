%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:40 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 257 expanded)
%              Number of clauses        :   44 (  93 expanded)
%              Number of leaves         :    8 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :  162 (2296 expanded)
%              Number of equality atoms :   31 ( 438 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & v6_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X1))
                         => ( ( X5 = X3
                              & X6 = X4 )
                           => k13_lattice3(X2,X3,X4) = k13_lattice3(X1,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_yellow_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v6_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ( ( X5 = X3
                                & X6 = X4 )
                             => k13_lattice3(X2,X3,X4) = k13_lattice3(X1,X5,X6) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_yellow_0])).

fof(c_0_9,negated_conjecture,
    ( v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & v5_orders_2(esk2_0)
    & v1_lattice3(esk2_0)
    & l1_orders_2(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v4_yellow_0(esk3_0,esk2_0)
    & v6_yellow_0(esk3_0,esk2_0)
    & m1_yellow_0(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk2_0))
    & esk6_0 = esk4_0
    & esk7_0 = esk5_0
    & k13_lattice3(esk3_0,esk4_0,esk5_0) != k13_lattice3(esk2_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_10,plain,(
    ! [X17,X18,X19] :
      ( v1_xboole_0(X17)
      | ~ m1_subset_1(X18,X17)
      | ~ m1_subset_1(X19,X17)
      | k7_domain_1(X17,X18,X19) = k2_tarski(X18,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_15,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12]),
    [final]).

fof(c_0_17,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X13,X14)
      | v1_xboole_0(X14)
      | r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_22,plain,(
    ! [X20] :
      ( ~ l1_orders_2(X20)
      | ~ v1_lattice3(X20)
      | ~ v2_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_23,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk2_0),X1,esk4_0) = k2_tarski(X1,esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk3_0),X1,esk4_0) = k2_tarski(X1,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_18]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk2_0),X1,esk7_0) = k2_tarski(X1,esk7_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_19]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk3_0),X1,esk7_0) = k2_tarski(X1,esk7_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_20]),
    [final]).

cnf(c_0_28,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21]),
    [final]).

fof(c_0_29,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_30,plain,(
    ! [X15] :
      ( v2_struct_0(X15)
      | ~ l1_struct_0(X15)
      | ~ v1_xboole_0(u1_struct_0(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_31,plain,(
    ! [X16] :
      ( ~ l1_orders_2(X16)
      | l1_struct_0(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_32,negated_conjecture,
    ( k13_lattice3(esk3_0,esk4_0,esk5_0) != k13_lattice3(esk2_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk2_0),esk4_0,esk4_0) = k2_tarski(esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk2_0),esk7_0,esk4_0) = k2_tarski(esk4_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_24]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk3_0),esk4_0,esk4_0) = k2_tarski(esk4_0,esk4_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_18]),
    [final]).

cnf(c_0_39,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk3_0),esk7_0,esk4_0) = k2_tarski(esk4_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_24]),
    [final]).

cnf(c_0_40,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk2_0),esk4_0,esk7_0) = k2_tarski(esk4_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16]),
    [final]).

cnf(c_0_41,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk2_0),esk7_0,esk7_0) = k2_tarski(esk7_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_19]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk3_0),esk4_0,esk7_0) = k2_tarski(esk4_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_18]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk3_0),esk7_0,esk7_0) = k2_tarski(esk7_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20]),
    [final]).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_16]),
    [final]).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk4_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_18]),
    [final]).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19]),
    [final]).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk7_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_20]),
    [final]).

cnf(c_0_48,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30]),
    [final]).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31]),
    [final]).

cnf(c_0_51,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29]),
    [final]).

cnf(c_0_52,negated_conjecture,
    ( k13_lattice3(esk3_0,esk4_0,esk7_0) != k13_lattice3(esk2_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_14]),c_0_12]),
    [final]).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])]),
    [final]).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_55,negated_conjecture,
    ( m1_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_56,negated_conjecture,
    ( v6_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_57,negated_conjecture,
    ( v4_yellow_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_58,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_59,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_60,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:44:17 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(t71_yellow_0, conjecture, ![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&v6_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>((X5=X3&X6=X4)=>k13_lattice3(X2,X3,X4)=k13_lattice3(X1,X5,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_yellow_0)).
% 0.20/0.37  fof(redefinition_k7_domain_1, axiom, ![X1, X2, X3]:(((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))&m1_subset_1(X3,X1))=>k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_domain_1)).
% 0.20/0.37  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.20/0.37  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.37  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.20/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.20/0.37  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.20/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v4_orders_2(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_yellow_0(X2,X1))&v6_yellow_0(X2,X1))&m1_yellow_0(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>((X5=X3&X6=X4)=>k13_lattice3(X2,X3,X4)=k13_lattice3(X1,X5,X6))))))))), inference(assume_negation,[status(cth)],[t71_yellow_0])).
% 0.20/0.37  fof(c_0_9, negated_conjecture, (((((v3_orders_2(esk2_0)&v4_orders_2(esk2_0))&v5_orders_2(esk2_0))&v1_lattice3(esk2_0))&l1_orders_2(esk2_0))&((((~v2_struct_0(esk3_0)&v4_yellow_0(esk3_0,esk2_0))&v6_yellow_0(esk3_0,esk2_0))&m1_yellow_0(esk3_0,esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk2_0))&(m1_subset_1(esk7_0,u1_struct_0(esk2_0))&((esk6_0=esk4_0&esk7_0=esk5_0)&k13_lattice3(esk3_0,esk4_0,esk5_0)!=k13_lattice3(esk2_0,esk6_0,esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.20/0.37  fof(c_0_10, plain, ![X17, X18, X19]:(v1_xboole_0(X17)|~m1_subset_1(X18,X17)|~m1_subset_1(X19,X17)|k7_domain_1(X17,X18,X19)=k2_tarski(X18,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (esk6_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (esk7_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_15, plain, (v1_xboole_0(X1)|k7_domain_1(X1,X2,X3)=k2_tarski(X2,X3)|~m1_subset_1(X2,X1)|~m1_subset_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.20/0.37  fof(c_0_17, plain, ![X11, X12]:k2_tarski(X11,X12)=k2_tarski(X12,X11), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.20/0.37  fof(c_0_21, plain, ![X13, X14]:(~m1_subset_1(X13,X14)|(v1_xboole_0(X14)|r2_hidden(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.37  fof(c_0_22, plain, ![X20]:(~l1_orders_2(X20)|(~v1_lattice3(X20)|~v2_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (k7_domain_1(u1_struct_0(esk2_0),X1,esk4_0)=k2_tarski(X1,esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_24, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (k7_domain_1(u1_struct_0(esk3_0),X1,esk4_0)=k2_tarski(X1,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_18]), ['final']).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (k7_domain_1(u1_struct_0(esk2_0),X1,esk7_0)=k2_tarski(X1,esk7_0)|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_19]), ['final']).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (k7_domain_1(u1_struct_0(esk3_0),X1,esk7_0)=k2_tarski(X1,esk7_0)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_28, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21]), ['final']).
% 0.20/0.37  fof(c_0_29, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_30, plain, ![X15]:(v2_struct_0(X15)|~l1_struct_0(X15)|~v1_xboole_0(u1_struct_0(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.20/0.37  fof(c_0_31, plain, ![X16]:(~l1_orders_2(X16)|l1_struct_0(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (k13_lattice3(esk3_0,esk4_0,esk5_0)!=k13_lattice3(esk2_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_33, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (v1_lattice3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (k7_domain_1(u1_struct_0(esk2_0),esk4_0,esk4_0)=k2_tarski(esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (k7_domain_1(u1_struct_0(esk2_0),esk7_0,esk4_0)=k2_tarski(esk4_0,esk7_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_24]), ['final']).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (k7_domain_1(u1_struct_0(esk3_0),esk4_0,esk4_0)=k2_tarski(esk4_0,esk4_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_25, c_0_18]), ['final']).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (k7_domain_1(u1_struct_0(esk3_0),esk7_0,esk4_0)=k2_tarski(esk4_0,esk7_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_24]), ['final']).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (k7_domain_1(u1_struct_0(esk2_0),esk4_0,esk7_0)=k2_tarski(esk4_0,esk7_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (k7_domain_1(u1_struct_0(esk2_0),esk7_0,esk7_0)=k2_tarski(esk7_0,esk7_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_26, c_0_19]), ['final']).
% 0.20/0.37  cnf(c_0_42, negated_conjecture, (k7_domain_1(u1_struct_0(esk3_0),esk4_0,esk7_0)=k2_tarski(esk4_0,esk7_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_18]), ['final']).
% 0.20/0.37  cnf(c_0_43, negated_conjecture, (k7_domain_1(u1_struct_0(esk3_0),esk7_0,esk7_0)=k2_tarski(esk7_0,esk7_0)|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_27, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk2_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_16]), ['final']).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk4_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_18]), ['final']).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk2_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_19]), ['final']).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(esk7_0,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_28, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_48, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_49, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_30]), ['final']).
% 0.20/0.37  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31]), ['final']).
% 0.20/0.37  cnf(c_0_51, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29]), ['final']).
% 0.20/0.37  cnf(c_0_52, negated_conjecture, (k13_lattice3(esk3_0,esk4_0,esk7_0)!=k13_lattice3(esk2_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_14]), c_0_12]), ['final']).
% 0.20/0.37  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])]), ['final']).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_55, negated_conjecture, (m1_yellow_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_56, negated_conjecture, (v6_yellow_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_57, negated_conjecture, (v4_yellow_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_58, negated_conjecture, (v5_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_59, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_60, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 61
% 0.20/0.37  # Proof object clause steps            : 44
% 0.20/0.37  # Proof object formula steps           : 17
% 0.20/0.37  # Proof object conjectures             : 39
% 0.20/0.37  # Proof object clause conjectures      : 36
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 24
% 0.20/0.37  # Proof object initial formulas used   : 8
% 0.20/0.37  # Proof object generating inferences   : 17
% 0.20/0.37  # Proof object simplifying inferences  : 8
% 0.20/0.37  # Parsed axioms                        : 8
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 24
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 24
% 0.20/0.37  # Processed clauses                    : 65
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 65
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 22
% 0.20/0.37  # ...of the previous two non-trivial   : 17
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 22
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 0
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 41
% 0.20/0.37  #    Positive orientable unit clauses  : 14
% 0.20/0.37  #    Positive unorientable unit clauses: 1
% 0.20/0.37  #    Negative unit clauses             : 3
% 0.20/0.37  #    Non-unit-clauses                  : 23
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 24
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 20
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 10
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 2
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1706
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.028 s
% 0.20/0.37  # System time              : 0.005 s
% 0.20/0.37  # Total time               : 0.032 s
% 0.20/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
