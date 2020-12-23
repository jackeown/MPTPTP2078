%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:35 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   22 (  59 expanded)
%              Number of clauses        :   17 (  19 expanded)
%              Number of leaves         :    2 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :  134 ( 632 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r2_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r1_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(t76_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v25_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_waybel_0)).

fof(c_0_2,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))
        | ~ r2_yellow_0(X5,X6)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( r1_lattice3(X5,X6,esk1_2(X5,X6))
        | ~ r2_yellow_0(X5,X6)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ m1_subset_1(X8,u1_struct_0(X5))
        | ~ r1_lattice3(X5,X6,X8)
        | r1_orders_2(X5,X8,esk1_2(X5,X6))
        | ~ r2_yellow_0(X5,X6)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( m1_subset_1(esk2_3(X5,X9,X10),u1_struct_0(X5))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r1_lattice3(X5,X9,X10)
        | r2_yellow_0(X5,X9)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( r1_lattice3(X5,X9,esk2_3(X5,X9,X10))
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r1_lattice3(X5,X9,X10)
        | r2_yellow_0(X5,X9)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) )
      & ( ~ r1_orders_2(X5,esk2_3(X5,X9,X10),X10)
        | ~ m1_subset_1(X10,u1_struct_0(X5))
        | ~ r1_lattice3(X5,X9,X10)
        | r2_yellow_0(X5,X9)
        | ~ v5_orders_2(X5)
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).

cnf(c_0_3,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_4,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v25_waybel_0(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => r2_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t76_waybel_0])).

cnf(c_0_6,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_orders_2(X1,esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_7,plain,
    ( r1_orders_2(X2,X1,esk1_2(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | ~ r2_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_8,plain,
    ( m1_subset_1(esk2_3(X1,X2,esk1_2(X1,X3)),u1_struct_0(X1))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_3,c_0_4]),
    [final]).

cnf(c_0_9,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

fof(c_0_10,negated_conjecture,(
    ! [X14] :
      ( ~ v2_struct_0(esk3_0)
      & v3_orders_2(esk3_0)
      & v5_orders_2(esk3_0)
      & l1_orders_2(esk3_0)
      & ( ~ v1_xboole_0(esk4_0)
        | ~ v25_waybel_0(esk3_0) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v25_waybel_0(esk3_0) )
      & ( ~ r2_yellow_0(esk3_0,esk4_0)
        | ~ v25_waybel_0(esk3_0) )
      & ( v25_waybel_0(esk3_0)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | r2_yellow_0(esk3_0,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).

cnf(c_0_11,plain,
    ( r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X3,esk2_3(X1,X2,esk1_2(X1,X3)))
    | ~ r1_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_4]),c_0_8]),
    [final]).

cnf(c_0_12,plain,
    ( r1_lattice3(X1,X2,esk2_3(X1,X2,esk1_2(X1,X3)))
    | r2_yellow_0(X1,X2)
    | ~ r1_lattice3(X1,X2,esk1_2(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_4]),
    [final]).

cnf(c_0_13,plain,
    ( r1_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_2]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( v25_waybel_0(esk3_0)
    | v1_xboole_0(X1)
    | r2_yellow_0(esk3_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v25_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( ~ r2_yellow_0(esk3_0,esk4_0)
    | ~ v25_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ v25_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:26:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.027 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # No proof found!
% 0.13/0.36  # SZS status CounterSatisfiable
% 0.13/0.36  # SZS output start Saturation
% 0.13/0.36  fof(t16_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r2_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r1_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X4)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_yellow_0)).
% 0.13/0.36  fof(t76_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v25_waybel_0(X1)<=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r2_yellow_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_waybel_0)).
% 0.13/0.36  fof(c_0_2, plain, ![X5, X6, X8, X9, X10]:((((m1_subset_1(esk1_2(X5,X6),u1_struct_0(X5))|~r2_yellow_0(X5,X6)|(~v5_orders_2(X5)|~l1_orders_2(X5)))&(r1_lattice3(X5,X6,esk1_2(X5,X6))|~r2_yellow_0(X5,X6)|(~v5_orders_2(X5)|~l1_orders_2(X5))))&(~m1_subset_1(X8,u1_struct_0(X5))|(~r1_lattice3(X5,X6,X8)|r1_orders_2(X5,X8,esk1_2(X5,X6)))|~r2_yellow_0(X5,X6)|(~v5_orders_2(X5)|~l1_orders_2(X5))))&((m1_subset_1(esk2_3(X5,X9,X10),u1_struct_0(X5))|(~m1_subset_1(X10,u1_struct_0(X5))|~r1_lattice3(X5,X9,X10))|r2_yellow_0(X5,X9)|(~v5_orders_2(X5)|~l1_orders_2(X5)))&((r1_lattice3(X5,X9,esk2_3(X5,X9,X10))|(~m1_subset_1(X10,u1_struct_0(X5))|~r1_lattice3(X5,X9,X10))|r2_yellow_0(X5,X9)|(~v5_orders_2(X5)|~l1_orders_2(X5)))&(~r1_orders_2(X5,esk2_3(X5,X9,X10),X10)|(~m1_subset_1(X10,u1_struct_0(X5))|~r1_lattice3(X5,X9,X10))|r2_yellow_0(X5,X9)|(~v5_orders_2(X5)|~l1_orders_2(X5)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_yellow_0])])])])])])).
% 0.13/0.36  cnf(c_0_3, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_4, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  fof(c_0_5, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v25_waybel_0(X1)<=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r2_yellow_0(X1,X2))))), inference(assume_negation,[status(cth)],[t76_waybel_0])).
% 0.13/0.36  cnf(c_0_6, plain, (r2_yellow_0(X1,X2)|~r1_orders_2(X1,esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_7, plain, (r1_orders_2(X2,X1,esk1_2(X2,X3))|~m1_subset_1(X1,u1_struct_0(X2))|~r1_lattice3(X2,X3,X1)|~r2_yellow_0(X2,X3)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_8, plain, (m1_subset_1(esk2_3(X1,X2,esk1_2(X1,X3)),u1_struct_0(X1))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk1_2(X1,X3))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(spm,[status(thm)],[c_0_3, c_0_4]), ['final']).
% 0.13/0.36  cnf(c_0_9, plain, (r1_lattice3(X1,X2,esk2_3(X1,X2,X3))|r2_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  fof(c_0_10, negated_conjecture, ![X14]:((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&((((~v1_xboole_0(esk4_0)|~v25_waybel_0(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v25_waybel_0(esk3_0)))&(~r2_yellow_0(esk3_0,esk4_0)|~v25_waybel_0(esk3_0)))&(v25_waybel_0(esk3_0)|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(esk3_0)))|r2_yellow_0(esk3_0,X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])])).
% 0.13/0.36  cnf(c_0_11, plain, (r2_yellow_0(X1,X2)|~r1_lattice3(X1,X3,esk2_3(X1,X2,esk1_2(X1,X3)))|~r1_lattice3(X1,X2,esk1_2(X1,X3))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_4]), c_0_8]), ['final']).
% 0.13/0.36  cnf(c_0_12, plain, (r1_lattice3(X1,X2,esk2_3(X1,X2,esk1_2(X1,X3)))|r2_yellow_0(X1,X2)|~r1_lattice3(X1,X2,esk1_2(X1,X3))|~r2_yellow_0(X1,X3)|~l1_orders_2(X1)|~v5_orders_2(X1)), inference(spm,[status(thm)],[c_0_9, c_0_4]), ['final']).
% 0.13/0.36  cnf(c_0_13, plain, (r1_lattice3(X1,X2,esk1_2(X1,X2))|~r2_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
% 0.13/0.36  cnf(c_0_14, negated_conjecture, (v25_waybel_0(esk3_0)|v1_xboole_0(X1)|r2_yellow_0(esk3_0,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v25_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_16, negated_conjecture, (~r2_yellow_0(esk3_0,esk4_0)|~v25_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_17, negated_conjecture, (~v1_xboole_0(esk4_0)|~v25_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_19, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  cnf(c_0_21, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10]), ['final']).
% 0.13/0.36  # SZS output end Saturation
% 0.13/0.36  # Proof object total steps             : 22
% 0.13/0.36  # Proof object clause steps            : 17
% 0.13/0.36  # Proof object formula steps           : 5
% 0.13/0.36  # Proof object conjectures             : 11
% 0.13/0.36  # Proof object clause conjectures      : 8
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 14
% 0.13/0.36  # Proof object initial formulas used   : 2
% 0.13/0.36  # Proof object generating inferences   : 3
% 0.13/0.36  # Proof object simplifying inferences  : 2
% 0.13/0.36  # Parsed axioms                        : 2
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 14
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 14
% 0.13/0.36  # Processed clauses                    : 31
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 0
% 0.13/0.36  # ...remaining for further processing  : 31
% 0.13/0.36  # Other redundant clauses eliminated   : 0
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 0
% 0.13/0.36  # Generated clauses                    : 6
% 0.13/0.36  # ...of the previous two non-trivial   : 3
% 0.13/0.36  # Contextual simplify-reflections      : 2
% 0.13/0.36  # Paramodulations                      : 6
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 0
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 17
% 0.13/0.36  #    Positive orientable unit clauses  : 3
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 1
% 0.13/0.36  #    Non-unit-clauses                  : 13
% 0.13/0.36  # Current number of unprocessed clauses: 0
% 0.13/0.36  # ...number of literals in the above   : 0
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 14
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 35
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 8
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.36  # Unit Clause-clause subsumption calls : 0
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 0
% 0.13/0.36  # BW rewrite match successes           : 0
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1402
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.026 s
% 0.13/0.36  # System time              : 0.005 s
% 0.13/0.36  # Total time               : 0.031 s
% 0.13/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
