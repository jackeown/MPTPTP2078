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

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   23 (  59 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    3 (  16 expanded)
%              Depth                    :    3
%              Number of atoms          :  109 ( 551 expanded)
%              Number of equality atoms :    6 (  46 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t48_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v14_waybel_0(X2,X1)
          <=> ? [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
                & X2 = k5_waybel_0(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_waybel_0)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v14_waybel_0(X2,X1)
            <=> ? [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                  & X2 = k5_waybel_0(X1,X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t48_waybel_0])).

fof(c_0_4,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ r2_hidden(X10,X8)
        | r1_orders_2(X7,X10,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),X8)
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) )
      & ( ~ r1_orders_2(X7,esk1_3(X7,X8,X9),X9)
        | r2_lattice3(X7,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(X7))
        | ~ l1_orders_2(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

fof(c_0_5,plain,(
    ! [X5,X6] :
      ( v2_struct_0(X5)
      | ~ v3_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | r1_orders_2(X5,X6,X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X14] :
      ( ~ v2_struct_0(esk2_0)
      & v3_orders_2(esk2_0)
      & v4_orders_2(esk2_0)
      & l1_orders_2(esk2_0)
      & ~ v1_xboole_0(esk3_0)
      & v1_waybel_0(esk3_0,esk2_0)
      & v12_waybel_0(esk3_0,esk2_0)
      & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
      & ( ~ v14_waybel_0(esk3_0,esk2_0)
        | ~ m1_subset_1(X14,u1_struct_0(esk2_0))
        | esk3_0 != k5_waybel_0(esk2_0,X14) )
      & ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
        | v14_waybel_0(esk3_0,esk2_0) )
      & ( esk3_0 = k5_waybel_0(esk2_0,esk4_0)
        | v14_waybel_0(esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_7,plain,
    ( r1_orders_2(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,plain,
    ( r2_lattice3(X1,X2,X3)
    | ~ r1_orders_2(X1,esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( ~ v14_waybel_0(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | esk3_0 != k5_waybel_0(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    | v14_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( esk3_0 = k5_waybel_0(esk2_0,esk4_0)
    | v14_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( v12_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( v1_waybel_0(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t48_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&v12_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v14_waybel_0(X2,X1)<=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&X2=k5_waybel_0(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_waybel_0)).
% 0.13/0.37  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.13/0.37  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_orders_2)).
% 0.13/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&v12_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v14_waybel_0(X2,X1)<=>?[X3]:(m1_subset_1(X3,u1_struct_0(X1))&X2=k5_waybel_0(X1,X3)))))), inference(assume_negation,[status(cth)],[t48_waybel_0])).
% 0.13/0.37  fof(c_0_4, plain, ![X7, X8, X9, X10]:((~r2_lattice3(X7,X8,X9)|(~m1_subset_1(X10,u1_struct_0(X7))|(~r2_hidden(X10,X8)|r1_orders_2(X7,X10,X9)))|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((m1_subset_1(esk1_3(X7,X8,X9),u1_struct_0(X7))|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&((r2_hidden(esk1_3(X7,X8,X9),X8)|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))&(~r1_orders_2(X7,esk1_3(X7,X8,X9),X9)|r2_lattice3(X7,X8,X9)|~m1_subset_1(X9,u1_struct_0(X7))|~l1_orders_2(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.13/0.37  fof(c_0_5, plain, ![X5, X6]:(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|r1_orders_2(X5,X6,X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ![X14]:((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&((((~v1_xboole_0(esk3_0)&v1_waybel_0(esk3_0,esk2_0))&v12_waybel_0(esk3_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))&((~v14_waybel_0(esk3_0,esk2_0)|(~m1_subset_1(X14,u1_struct_0(esk2_0))|esk3_0!=k5_waybel_0(esk2_0,X14)))&((m1_subset_1(esk4_0,u1_struct_0(esk2_0))|v14_waybel_0(esk3_0,esk2_0))&(esk3_0=k5_waybel_0(esk2_0,esk4_0)|v14_waybel_0(esk3_0,esk2_0)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).
% 0.13/0.37  cnf(c_0_7, plain, (r1_orders_2(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_8, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_9, plain, (r2_lattice3(X1,X2,X3)|~r1_orders_2(X1,esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_10, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_11, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (~v14_waybel_0(esk3_0,esk2_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))|esk3_0!=k5_waybel_0(esk2_0,X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))|v14_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (esk3_0=k5_waybel_0(esk2_0,esk4_0)|v14_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (v12_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (v1_waybel_0(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 23
% 0.13/0.37  # Proof object clause steps            : 16
% 0.13/0.37  # Proof object formula steps           : 7
% 0.13/0.37  # Proof object conjectures             : 14
% 0.13/0.37  # Proof object clause conjectures      : 11
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 16
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 0
% 0.13/0.37  # Proof object simplifying inferences  : 0
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 16
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 16
% 0.13/0.37  # Processed clauses                    : 32
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 32
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 1
% 0.13/0.37  # ...of the previous two non-trivial   : 0
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 1
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 16
% 0.13/0.37  #    Positive orientable unit clauses  : 6
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 8
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 16
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 7
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 2
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 2
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1231
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.026 s
% 0.13/0.38  # System time              : 0.006 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
