%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:35 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   24 (  60 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    3 (  17 expanded)
%              Depth                    :    3
%              Number of atoms          :  159 ( 660 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t75_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v24_waybel_0(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r1_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_waybel_0)).

fof(t15_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( r1_yellow_0(X1,X2)
        <=> ? [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
              & r2_lattice3(X1,X2,X3)
              & ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r2_lattice3(X1,X2,X4)
                   => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ( v24_waybel_0(X1)
        <=> ! [X2] :
              ( ( ~ v1_xboole_0(X2)
                & v1_waybel_0(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
             => r1_yellow_0(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t75_waybel_0])).

fof(c_0_4,plain,(
    ! [X8,X9,X11,X12,X13] :
      ( ( m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))
        | ~ r1_yellow_0(X8,X9)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_lattice3(X8,X9,esk1_2(X8,X9))
        | ~ r1_yellow_0(X8,X9)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ m1_subset_1(X11,u1_struct_0(X8))
        | ~ r2_lattice3(X8,X9,X11)
        | r1_orders_2(X8,esk1_2(X8,X9),X11)
        | ~ r1_yellow_0(X8,X9)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( m1_subset_1(esk2_3(X8,X12,X13),u1_struct_0(X8))
        | ~ m1_subset_1(X13,u1_struct_0(X8))
        | ~ r2_lattice3(X8,X12,X13)
        | r1_yellow_0(X8,X12)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( r2_lattice3(X8,X12,esk2_3(X8,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X8))
        | ~ r2_lattice3(X8,X12,X13)
        | r1_yellow_0(X8,X12)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) )
      & ( ~ r1_orders_2(X8,X13,esk2_3(X8,X12,X13))
        | ~ m1_subset_1(X13,u1_struct_0(X8))
        | ~ r2_lattice3(X8,X12,X13)
        | r1_yellow_0(X8,X12)
        | ~ v5_orders_2(X8)
        | ~ l1_orders_2(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).

fof(c_0_5,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r3_orders_2(X5,X6,X7)
        | r1_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) )
      & ( ~ r1_orders_2(X5,X6,X7)
        | r3_orders_2(X5,X6,X7)
        | v2_struct_0(X5)
        | ~ v3_orders_2(X5)
        | ~ l1_orders_2(X5)
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

fof(c_0_6,negated_conjecture,(
    ! [X17] :
      ( ~ v2_struct_0(esk3_0)
      & v3_orders_2(esk3_0)
      & v5_orders_2(esk3_0)
      & l1_orders_2(esk3_0)
      & ( ~ v1_xboole_0(esk4_0)
        | ~ v24_waybel_0(esk3_0) )
      & ( v1_waybel_0(esk4_0,esk3_0)
        | ~ v24_waybel_0(esk3_0) )
      & ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v24_waybel_0(esk3_0) )
      & ( ~ r1_yellow_0(esk3_0,esk4_0)
        | ~ v24_waybel_0(esk3_0) )
      & ( v24_waybel_0(esk3_0)
        | v1_xboole_0(X17)
        | ~ v1_waybel_0(X17,esk3_0)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | r1_yellow_0(esk3_0,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_7,plain,
    ( r1_yellow_0(X1,X3)
    | ~ r1_orders_2(X1,X2,esk2_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,plain,
    ( r2_lattice3(X1,X2,esk2_3(X1,X2,X3))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_9,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ r1_yellow_0(X2,X3)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_10,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_11,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))
    | r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_13,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_14,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ r1_yellow_0(X1,X2)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( ~ r1_yellow_0(esk3_0,esk4_0)
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( v24_waybel_0(esk3_0)
    | v1_xboole_0(X1)
    | r1_yellow_0(esk3_0,X1)
    | ~ v1_waybel_0(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( v1_waybel_0(esk4_0,esk3_0)
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ v24_waybel_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S064A
% 0.13/0.37  # and selection function SelectComplexG.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t75_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v24_waybel_0(X1)<=>![X2]:(((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r1_yellow_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_waybel_0)).
% 0.13/0.37  fof(t15_yellow_0, axiom, ![X1]:((v5_orders_2(X1)&l1_orders_2(X1))=>![X2]:(r1_yellow_0(X1,X2)<=>?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow_0)).
% 0.13/0.37  fof(redefinition_r3_orders_2, axiom, ![X1, X2, X3]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>(r3_orders_2(X1,X2,X3)<=>r1_orders_2(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 0.13/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>(v24_waybel_0(X1)<=>![X2]:(((~(v1_xboole_0(X2))&v1_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>r1_yellow_0(X1,X2))))), inference(assume_negation,[status(cth)],[t75_waybel_0])).
% 0.13/0.37  fof(c_0_4, plain, ![X8, X9, X11, X12, X13]:((((m1_subset_1(esk1_2(X8,X9),u1_struct_0(X8))|~r1_yellow_0(X8,X9)|(~v5_orders_2(X8)|~l1_orders_2(X8)))&(r2_lattice3(X8,X9,esk1_2(X8,X9))|~r1_yellow_0(X8,X9)|(~v5_orders_2(X8)|~l1_orders_2(X8))))&(~m1_subset_1(X11,u1_struct_0(X8))|(~r2_lattice3(X8,X9,X11)|r1_orders_2(X8,esk1_2(X8,X9),X11))|~r1_yellow_0(X8,X9)|(~v5_orders_2(X8)|~l1_orders_2(X8))))&((m1_subset_1(esk2_3(X8,X12,X13),u1_struct_0(X8))|(~m1_subset_1(X13,u1_struct_0(X8))|~r2_lattice3(X8,X12,X13))|r1_yellow_0(X8,X12)|(~v5_orders_2(X8)|~l1_orders_2(X8)))&((r2_lattice3(X8,X12,esk2_3(X8,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X8))|~r2_lattice3(X8,X12,X13))|r1_yellow_0(X8,X12)|(~v5_orders_2(X8)|~l1_orders_2(X8)))&(~r1_orders_2(X8,X13,esk2_3(X8,X12,X13))|(~m1_subset_1(X13,u1_struct_0(X8))|~r2_lattice3(X8,X12,X13))|r1_yellow_0(X8,X12)|(~v5_orders_2(X8)|~l1_orders_2(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_yellow_0])])])])])])).
% 0.13/0.37  fof(c_0_5, plain, ![X5, X6, X7]:((~r3_orders_2(X5,X6,X7)|r1_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))&(~r1_orders_2(X5,X6,X7)|r3_orders_2(X5,X6,X7)|(v2_struct_0(X5)|~v3_orders_2(X5)|~l1_orders_2(X5)|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X7,u1_struct_0(X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ![X17]:((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(((((~v1_xboole_0(esk4_0)|~v24_waybel_0(esk3_0))&(v1_waybel_0(esk4_0,esk3_0)|~v24_waybel_0(esk3_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v24_waybel_0(esk3_0)))&(~r1_yellow_0(esk3_0,esk4_0)|~v24_waybel_0(esk3_0)))&(v24_waybel_0(esk3_0)|(v1_xboole_0(X17)|~v1_waybel_0(X17,esk3_0)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(esk3_0)))|r1_yellow_0(esk3_0,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).
% 0.13/0.37  cnf(c_0_7, plain, (r1_yellow_0(X1,X3)|~r1_orders_2(X1,X2,esk2_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_8, plain, (r2_lattice3(X1,X2,esk2_3(X1,X2,X3))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_9, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~r1_yellow_0(X2,X3)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_10, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r3_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.37  cnf(c_0_11, plain, (r3_orders_2(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X2,X3)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.13/0.37  cnf(c_0_12, plain, (m1_subset_1(esk2_3(X1,X2,X3),u1_struct_0(X1))|r1_yellow_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_13, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_14, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~r1_yellow_0(X1,X2)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (~r1_yellow_0(esk3_0,esk4_0)|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v24_waybel_0(esk3_0)|v1_xboole_0(X1)|r1_yellow_0(esk3_0,X1)|~v1_waybel_0(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (v1_waybel_0(esk4_0,esk3_0)|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (~v1_xboole_0(esk4_0)|~v24_waybel_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  # SZS output end Saturation
% 0.13/0.37  # Proof object total steps             : 24
% 0.13/0.37  # Proof object clause steps            : 17
% 0.13/0.37  # Proof object formula steps           : 7
% 0.13/0.37  # Proof object conjectures             : 12
% 0.13/0.37  # Proof object clause conjectures      : 9
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 17
% 0.13/0.37  # Proof object initial formulas used   : 3
% 0.13/0.37  # Proof object generating inferences   : 0
% 0.13/0.37  # Proof object simplifying inferences  : 0
% 0.13/0.37  # Parsed axioms                        : 3
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 17
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 17
% 0.13/0.37  # Processed clauses                    : 34
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 34
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 0
% 0.13/0.37  # ...of the previous two non-trivial   : 0
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 0
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
% 0.13/0.37  # Current number of processed clauses  : 17
% 0.13/0.37  #    Positive orientable unit clauses  : 3
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 13
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 35
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 8
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1666
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.030 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.032 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
