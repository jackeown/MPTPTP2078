%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:20 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 187 expanded)
%              Number of clauses        :   26 (  67 expanded)
%              Number of leaves         :    4 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  182 (1295 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_lattice3(X1,X2,X3)
              <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(t26_orders_2,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( ( r1_orders_2(X1,X2,X3)
                      & r1_orders_2(X1,X3,X4) )
                   => r1_orders_2(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(t9_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => ! [X4] :
              ( m1_subset_1(X4,u1_struct_0(X1))
             => ( ( r1_lattice3(X1,X3,X4)
                 => r1_lattice3(X1,X2,X4) )
                & ( r2_lattice3(X1,X3,X4)
                 => r2_lattice3(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X3)
                <=> r1_lattice3(X1,k4_waybel_0(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_waybel_0])).

fof(c_0_5,plain,(
    ! [X9,X10,X11,X12] :
      ( ( ~ r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | ~ r2_hidden(X12,X10)
        | r1_orders_2(X9,X11,X12)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_3(X9,X10,X11),X10)
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) )
      & ( ~ r1_orders_2(X9,X11,esk1_3(X9,X10,X11))
        | r1_lattice3(X9,X10,X11)
        | ~ m1_subset_1(X11,u1_struct_0(X9))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v3_orders_2(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & ( ~ r1_lattice3(esk2_0,esk3_0,esk4_0)
      | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) )
    & ( r1_lattice3(esk2_0,esk3_0,esk4_0)
      | r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

cnf(c_0_7,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8] :
      ( ~ v4_orders_2(X5)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ r1_orders_2(X5,X6,X7)
      | ~ r1_orders_2(X5,X7,X8)
      | r1_orders_2(X5,X6,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_lattice3(esk2_0,esk3_0,esk4_0)
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( r1_lattice3(esk2_0,X1,X2)
    | m1_subset_1(esk1_3(esk2_0,X1,X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_13,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X3,X2)
    | ~ r1_orders_2(esk2_0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_8])]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_11]),c_0_12])]),
    [final]).

cnf(c_0_18,plain,
    ( r1_orders_2(X1,X3,X4)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]),
    [final]).

cnf(c_0_21,plain,
    ( r1_lattice3(X1,X2,X3)
    | r1_orders_2(X4,X5,esk1_3(X1,X2,X3))
    | ~ r1_lattice3(X4,X2,X5)
    | ~ m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X4)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

fof(c_0_22,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ r1_lattice3(X14,X16,X17)
        | r1_lattice3(X14,X15,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r1_tarski(X15,X16)
        | ~ l1_orders_2(X14) )
      & ( ~ r2_lattice3(X14,X16,X17)
        | r2_lattice3(X14,X15,X17)
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r1_tarski(X15,X16)
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).

cnf(c_0_23,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_12]),c_0_8])]),c_0_17]),
    [final]).

cnf(c_0_24,plain,
    ( r2_lattice3(X1,X4,X3)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)
    | r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),u1_struct_0(esk2_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_11]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk4_0)
    | ~ r2_lattice3(esk2_0,X2,esk4_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_12]),c_0_8])]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))
    | ~ r2_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_17]),c_0_8])]),
    [final]).

cnf(c_0_29,plain,
    ( r1_lattice3(X1,X3,X2)
    | ~ r1_orders_2(X1,X2,esk1_3(X1,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X4,X3)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r1_tarski(X4,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(esk2_0,esk3_0,esk4_0)
    | r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S033I
% 0.19/0.38  # and selection function PSelectUnlessUniqMax.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.032 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # No proof found!
% 0.19/0.38  # SZS status CounterSatisfiable
% 0.19/0.38  # SZS output start Saturation
% 0.19/0.38  fof(t36_waybel_0, conjecture, ![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>r1_lattice3(X1,k4_waybel_0(X1,X2),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_waybel_0)).
% 0.19/0.38  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattice3)).
% 0.19/0.38  fof(t26_orders_2, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 0.19/0.38  fof(t9_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_lattice3(X1,X3,X4)=>r1_lattice3(X1,X2,X4))&(r2_lattice3(X1,X3,X4)=>r2_lattice3(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_yellow_0)).
% 0.19/0.38  fof(c_0_4, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>r1_lattice3(X1,k4_waybel_0(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t36_waybel_0])).
% 0.19/0.38  fof(c_0_5, plain, ![X9, X10, X11, X12]:((~r1_lattice3(X9,X10,X11)|(~m1_subset_1(X12,u1_struct_0(X9))|(~r2_hidden(X12,X10)|r1_orders_2(X9,X11,X12)))|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((m1_subset_1(esk1_3(X9,X10,X11),u1_struct_0(X9))|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&((r2_hidden(esk1_3(X9,X10,X11),X10)|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))&(~r1_orders_2(X9,X11,esk1_3(X9,X10,X11))|r1_lattice3(X9,X10,X11)|~m1_subset_1(X11,u1_struct_0(X9))|~l1_orders_2(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.19/0.38  fof(c_0_6, negated_conjecture, ((((~v2_struct_0(esk2_0)&v3_orders_2(esk2_0))&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&((~r1_lattice3(esk2_0,esk3_0,esk4_0)|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))&(r1_lattice3(esk2_0,esk3_0,esk4_0)|r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.19/0.38  cnf(c_0_7, plain, (m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_8, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  fof(c_0_9, plain, ![X5, X6, X7, X8]:(~v4_orders_2(X5)|~l1_orders_2(X5)|(~m1_subset_1(X6,u1_struct_0(X5))|(~m1_subset_1(X7,u1_struct_0(X5))|(~m1_subset_1(X8,u1_struct_0(X5))|(~r1_orders_2(X5,X6,X7)|~r1_orders_2(X5,X7,X8)|r1_orders_2(X5,X6,X8)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).
% 0.19/0.38  cnf(c_0_10, negated_conjecture, (~r1_lattice3(esk2_0,esk3_0,esk4_0)|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_11, negated_conjecture, (r1_lattice3(esk2_0,X1,X2)|m1_subset_1(esk1_3(esk2_0,X1,X2),u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_7, c_0_8]), ['final']).
% 0.19/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_13, plain, (r1_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), ['final']).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk2_0,X1,X2)|~r1_orders_2(esk2_0,X3,X2)|~r1_orders_2(esk2_0,X1,X3)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X3,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_8])]), ['final']).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_11]), c_0_12])]), ['final']).
% 0.19/0.38  cnf(c_0_18, plain, (r1_orders_2(X1,X3,X4)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~r2_hidden(X4,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_19, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_21, plain, (r1_lattice3(X1,X2,X3)|r1_orders_2(X4,X5,esk1_3(X1,X2,X3))|~r1_lattice3(X4,X2,X5)|~m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X4))|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X4)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.19/0.38  fof(c_0_22, plain, ![X14, X15, X16, X17]:((~r1_lattice3(X14,X16,X17)|r1_lattice3(X14,X15,X17)|~m1_subset_1(X17,u1_struct_0(X14))|~r1_tarski(X15,X16)|~l1_orders_2(X14))&(~r2_lattice3(X14,X16,X17)|r2_lattice3(X14,X15,X17)|~m1_subset_1(X17,u1_struct_0(X14))|~r1_tarski(X15,X16)|~l1_orders_2(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_yellow_0])])])])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_12]), c_0_8])]), c_0_17]), ['final']).
% 0.19/0.38  cnf(c_0_24, plain, (r2_lattice3(X1,X4,X3)|~r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)|r1_orders_2(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),X2),u1_struct_0(esk2_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_23, c_0_11]), ['final']).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X2,esk4_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_16, c_0_12]), ['final']).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (r2_lattice3(esk2_0,X1,esk4_0)|~r2_lattice3(esk2_0,X2,esk4_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_12]), c_0_8])]), ['final']).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_lattice3(esk2_0,X1,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),u1_struct_0(esk2_0))|~r2_lattice3(esk2_0,X2,esk1_3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0))|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_17]), c_0_8])]), ['final']).
% 0.19/0.38  cnf(c_0_29, plain, (r1_lattice3(X1,X3,X2)|~r1_orders_2(X1,X2,esk1_3(X1,X3,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.19/0.38  cnf(c_0_30, plain, (r1_lattice3(X1,X4,X3)|~r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~r1_tarski(X4,X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_22]), ['final']).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r1_lattice3(esk2_0,esk3_0,esk4_0)|r1_lattice3(esk2_0,k4_waybel_0(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (v3_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.19/0.38  # SZS output end Saturation
% 0.19/0.38  # Proof object total steps             : 35
% 0.19/0.38  # Proof object clause steps            : 26
% 0.19/0.38  # Proof object formula steps           : 9
% 0.19/0.38  # Proof object conjectures             : 21
% 0.19/0.38  # Proof object clause conjectures      : 18
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 15
% 0.19/0.38  # Proof object initial formulas used   : 4
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 14
% 0.19/0.38  # Parsed axioms                        : 4
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 15
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 15
% 0.19/0.38  # Processed clauses                    : 43
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 2
% 0.19/0.38  # ...remaining for further processing  : 41
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 0
% 0.19/0.38  # Generated clauses                    : 16
% 0.19/0.38  # ...of the previous two non-trivial   : 13
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 16
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 26
% 0.19/0.38  #    Positive orientable unit clauses  : 5
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 20
% 0.19/0.38  # Current number of unprocessed clauses: 0
% 0.19/0.38  # ...number of literals in the above   : 0
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 15
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 181
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 22
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.38  # Unit Clause-clause subsumption calls : 0
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 0
% 0.19/0.38  # BW rewrite match successes           : 0
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 2161
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.038 s
% 0.19/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
