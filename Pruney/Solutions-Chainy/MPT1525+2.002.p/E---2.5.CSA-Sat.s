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
% DateTime   : Thu Dec  3 11:15:11 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 486 expanded)
%              Number of clauses        :   33 ( 201 expanded)
%              Number of leaves         :    5 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 (1893 expanded)
%              Number of equality atoms :   22 ( 446 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
              & v3_lattice3(X1) )
           => v3_lattice3(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_0)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(d12_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_lattice3(X1)
      <=> ! [X2] :
          ? [X3] :
            ( m1_subset_1(X3,u1_struct_0(X1))
            & r2_lattice3(X1,X2,X3)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_lattice3(X1,X2,X4)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_lattice3)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & v3_lattice3(X1) )
             => v3_lattice3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow_0])).

fof(c_0_6,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_7,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & l1_orders_2(esk5_0)
    & g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    & v3_lattice3(esk4_0)
    & ~ v3_lattice3(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( X10 = X12
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( u1_orders_2(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) != g1_orders_2(X2,X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk5_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]),
    [final]).

fof(c_0_17,plain,(
    ! [X13,X14,X16,X18] :
      ( ( m1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))
        | ~ v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,X14,esk1_2(X13,X14))
        | ~ v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X16,u1_struct_0(X13))
        | ~ r2_lattice3(X13,X14,X16)
        | r1_orders_2(X13,esk1_2(X13,X14),X16)
        | ~ v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk3_2(X13,X18),u1_struct_0(X13))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r2_lattice3(X13,esk2_1(X13),X18)
        | v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( r2_lattice3(X13,esk2_1(X13),esk3_2(X13,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r2_lattice3(X13,esk2_1(X13),X18)
        | v3_lattice3(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_orders_2(X13,X18,esk3_2(X13,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r2_lattice3(X13,esk2_1(X13),X18)
        | v3_lattice3(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_18,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) != g1_orders_2(X1,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_12]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_14,c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v3_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

fof(c_0_23,plain,(
    ! [X5,X6,X7] :
      ( ( ~ r1_orders_2(X5,X6,X7)
        | r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) )
      & ( ~ r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))
        | r1_orders_2(X5,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(X5))
        | ~ m1_subset_1(X6,u1_struct_0(X5))
        | ~ l1_orders_2(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_24,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),X2)
    | ~ r2_lattice3(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21]),c_0_22])]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_16]),c_0_22])]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X2))
    | ~ r2_lattice3(esk4_0,X1,esk1_2(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]),
    [final]).

cnf(c_0_32,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(esk4_0,X2)),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk4_0,X1,esk1_2(esk4_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_21]),c_0_22])]),
    [final]).

cnf(c_0_35,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23]),
    [final]).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(esk4_0,X1),esk1_2(esk4_0,X1)),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_29])]),
    [final]).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,esk1_2(esk4_0,X2)),u1_orders_2(esk5_0))
    | ~ r1_orders_2(esk5_0,X1,esk1_2(esk4_0,X2))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_29]),c_0_10])]),
    [final]).

cnf(c_0_38,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk5_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_16]),c_0_22])]),c_0_25]),c_0_25]),
    [final]).

cnf(c_0_39,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_40,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_41,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17]),
    [final]).

cnf(c_0_42,negated_conjecture,
    ( ~ v3_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_43,negated_conjecture,
    ( r1_orders_2(esk5_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_29]),c_0_10])]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S031A
% 0.13/0.37  # and selection function PSelectStrongRRNonRROptimalLit.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # No proof found!
% 0.13/0.37  # SZS status CounterSatisfiable
% 0.13/0.37  # SZS output start Saturation
% 0.13/0.37  fof(t3_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))&v3_lattice3(X1))=>v3_lattice3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_0)).
% 0.13/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.13/0.37  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.13/0.37  fof(d12_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v3_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_lattice3)).
% 0.13/0.37  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.13/0.37  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))&v3_lattice3(X1))=>v3_lattice3(X2))))), inference(assume_negation,[status(cth)],[t3_yellow_0])).
% 0.13/0.37  fof(c_0_6, plain, ![X8]:(~l1_orders_2(X8)|m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.13/0.37  fof(c_0_7, negated_conjecture, (l1_orders_2(esk4_0)&(l1_orders_2(esk5_0)&((g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))&v3_lattice3(esk4_0))&~v3_lattice3(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X9, X10, X11, X12]:((X9=X11|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))&(X10=X12|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.13/0.37  cnf(c_0_9, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_11, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.13/0.37  cnf(c_0_13, negated_conjecture, (u1_orders_2(esk5_0)=X1|g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))!=g1_orders_2(X2,X1)), inference(spm,[status(thm)],[c_0_11, c_0_12]), ['final']).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_15, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (u1_orders_2(esk4_0)=u1_orders_2(esk5_0)), inference(spm,[status(thm)],[c_0_13, c_0_14]), ['final']).
% 0.13/0.37  fof(c_0_17, plain, ![X13, X14, X16, X18]:((((m1_subset_1(esk1_2(X13,X14),u1_struct_0(X13))|~v3_lattice3(X13)|~l1_orders_2(X13))&(r2_lattice3(X13,X14,esk1_2(X13,X14))|~v3_lattice3(X13)|~l1_orders_2(X13)))&(~m1_subset_1(X16,u1_struct_0(X13))|(~r2_lattice3(X13,X14,X16)|r1_orders_2(X13,esk1_2(X13,X14),X16))|~v3_lattice3(X13)|~l1_orders_2(X13)))&((m1_subset_1(esk3_2(X13,X18),u1_struct_0(X13))|(~m1_subset_1(X18,u1_struct_0(X13))|~r2_lattice3(X13,esk2_1(X13),X18))|v3_lattice3(X13)|~l1_orders_2(X13))&((r2_lattice3(X13,esk2_1(X13),esk3_2(X13,X18))|(~m1_subset_1(X18,u1_struct_0(X13))|~r2_lattice3(X13,esk2_1(X13),X18))|v3_lattice3(X13)|~l1_orders_2(X13))&(~r1_orders_2(X13,X18,esk3_2(X13,X18))|(~m1_subset_1(X18,u1_struct_0(X13))|~r2_lattice3(X13,esk2_1(X13),X18))|v3_lattice3(X13)|~l1_orders_2(X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (u1_struct_0(esk5_0)=X1|g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))!=g1_orders_2(X1,X2)), inference(spm,[status(thm)],[c_0_15, c_0_12]), ['final']).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk5_0))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))), inference(rw,[status(thm)],[c_0_14, c_0_16])).
% 0.13/0.37  cnf(c_0_20, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v3_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.37  fof(c_0_23, plain, ![X5, X6, X7]:((~r1_orders_2(X5,X6,X7)|r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(~r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))|r1_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.13/0.37  cnf(c_0_24, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~v3_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19]), ['final']).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.37  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),X2)|~r2_lattice3(esk4_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_21]), c_0_22])]), ['final']).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_26, c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk5_0))|~r1_orders_2(esk4_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_16]), c_0_22])]), ['final']).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X2))|~r2_lattice3(esk4_0,X1,esk1_2(esk4_0,X2))), inference(spm,[status(thm)],[c_0_28, c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_32, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_2(esk4_0,X2)),u1_orders_2(esk5_0))|~r1_orders_2(esk4_0,X1,esk1_2(esk4_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_29]), ['final']).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_21]), c_0_22])]), ['final']).
% 0.13/0.38  cnf(c_0_35, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_23]), ['final']).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(esk4_0,X1),esk1_2(esk4_0,X1)),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_29])]), ['final']).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(k4_tarski(X1,esk1_2(esk4_0,X2)),u1_orders_2(esk5_0))|~r1_orders_2(esk5_0,X1,esk1_2(esk4_0,X2))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_29]), c_0_10])]), ['final']).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r1_orders_2(esk4_0,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk5_0))|~m1_subset_1(X2,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_16]), c_0_22])]), c_0_25]), c_0_25]), ['final']).
% 0.13/0.38  cnf(c_0_39, plain, (r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_40, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_41, plain, (v3_lattice3(X1)|~r1_orders_2(X1,X2,esk3_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_17]), ['final']).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (~v3_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (r1_orders_2(esk5_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_29]), c_0_10])]), ['final']).
% 0.13/0.38  # SZS output end Saturation
% 0.13/0.38  # Proof object total steps             : 44
% 0.13/0.38  # Proof object clause steps            : 33
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 25
% 0.13/0.38  # Proof object clause conjectures      : 22
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 16
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 24
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 16
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 16
% 0.13/0.38  # Processed clauses                    : 53
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 49
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 3
% 0.13/0.38  # Generated clauses                    : 27
% 0.13/0.38  # ...of the previous two non-trivial   : 22
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 25
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 30
% 0.13/0.38  #    Positive orientable unit clauses  : 10
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 19
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 30
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 9
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 4
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 2116
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.004 s
% 0.13/0.38  # Total time               : 0.034 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
