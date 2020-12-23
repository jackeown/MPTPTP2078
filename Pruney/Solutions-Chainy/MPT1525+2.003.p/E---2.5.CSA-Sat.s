%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:11 EST 2020

% Result     : CounterSatisfiable 0.12s
% Output     : Saturation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 121 expanded)
%              Number of clauses        :   25 (  48 expanded)
%              Number of leaves         :    4 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 566 expanded)
%              Number of equality atoms :   22 (  99 expanded)
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

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
                & v3_lattice3(X1) )
             => v3_lattice3(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t3_yellow_0])).

fof(c_0_5,plain,(
    ! [X5] :
      ( ~ l1_orders_2(X5)
      | m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & l1_orders_2(esk5_0)
    & g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))
    & v3_lattice3(esk4_0)
    & ~ v3_lattice3(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9] :
      ( ( X6 = X8
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) )
      & ( X7 = X9
        | g1_orders_2(X6,X7) != g1_orders_2(X8,X9)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( u1_orders_2(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) != g1_orders_2(X2,X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( u1_orders_2(esk4_0) = u1_orders_2(esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13]),
    [final]).

fof(c_0_16,plain,(
    ! [X10,X11,X13,X15] :
      ( ( m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,X11,esk1_2(X10,X11))
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ m1_subset_1(X13,u1_struct_0(X10))
        | ~ r2_lattice3(X10,X11,X13)
        | r1_orders_2(X10,esk1_2(X10,X11),X13)
        | ~ v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( m1_subset_1(esk3_2(X10,X15),u1_struct_0(X10))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,esk2_1(X10),X15)
        | v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( r2_lattice3(X10,esk2_1(X10),esk3_2(X10,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,esk2_1(X10),X15)
        | v3_lattice3(X10)
        | ~ l1_orders_2(X10) )
      & ( ~ r1_orders_2(X10,X15,esk3_2(X10,X15))
        | ~ m1_subset_1(X15,u1_struct_0(X10))
        | ~ r2_lattice3(X10,esk2_1(X10),X15)
        | v3_lattice3(X10)
        | ~ l1_orders_2(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).

cnf(c_0_17,negated_conjecture,
    ( u1_struct_0(esk5_0) = X1
    | g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) != g1_orders_2(X1,X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_11]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk5_0)) = g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( v3_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_22,plain,
    ( r1_orders_2(X2,esk1_2(X2,X3),X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | ~ v3_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),X2)
    | ~ r2_lattice3(esk4_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_20]),c_0_21])]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X2))
    | ~ r2_lattice3(esk4_0,X1,esk1_2(esk4_0,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26]),
    [final]).

cnf(c_0_28,plain,
    ( r2_lattice3(X1,X2,esk1_2(X1,X2))
    | ~ v3_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_29,plain,
    ( r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_30,plain,
    ( m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))
    | v3_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_31,plain,
    ( v3_lattice3(X1)
    | ~ r1_orders_2(X1,X2,esk3_2(X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ r2_lattice3(X1,esk2_1(X1),X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( ~ v3_lattice3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_20]),c_0_21])]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S031A
% 0.12/0.37  # and selection function PSelectStrongRRNonRROptimalLit.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # No proof found!
% 0.12/0.37  # SZS status CounterSatisfiable
% 0.12/0.37  # SZS output start Saturation
% 0.12/0.37  fof(t3_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))&v3_lattice3(X1))=>v3_lattice3(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_0)).
% 0.12/0.37  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.12/0.37  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.12/0.37  fof(d12_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v3_lattice3(X1)<=>![X2]:?[X3]:((m1_subset_1(X3,u1_struct_0(X1))&r2_lattice3(X1,X2,X3))&![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X4)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_lattice3)).
% 0.12/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>((g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))&v3_lattice3(X1))=>v3_lattice3(X2))))), inference(assume_negation,[status(cth)],[t3_yellow_0])).
% 0.12/0.37  fof(c_0_5, plain, ![X5]:(~l1_orders_2(X5)|m1_subset_1(u1_orders_2(X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X5))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.12/0.37  fof(c_0_6, negated_conjecture, (l1_orders_2(esk4_0)&(l1_orders_2(esk5_0)&((g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))&v3_lattice3(esk4_0))&~v3_lattice3(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X6, X7, X8, X9]:((X6=X8|g1_orders_2(X6,X7)!=g1_orders_2(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))&(X7=X9|g1_orders_2(X6,X7)!=g1_orders_2(X8,X9)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.12/0.37  cnf(c_0_8, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.37  cnf(c_0_10, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_8, c_0_9]), ['final']).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (u1_orders_2(esk5_0)=X1|g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))!=g1_orders_2(X2,X1)), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk4_0))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_14, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (u1_orders_2(esk4_0)=u1_orders_2(esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13]), ['final']).
% 0.12/0.37  fof(c_0_16, plain, ![X10, X11, X13, X15]:((((m1_subset_1(esk1_2(X10,X11),u1_struct_0(X10))|~v3_lattice3(X10)|~l1_orders_2(X10))&(r2_lattice3(X10,X11,esk1_2(X10,X11))|~v3_lattice3(X10)|~l1_orders_2(X10)))&(~m1_subset_1(X13,u1_struct_0(X10))|(~r2_lattice3(X10,X11,X13)|r1_orders_2(X10,esk1_2(X10,X11),X13))|~v3_lattice3(X10)|~l1_orders_2(X10)))&((m1_subset_1(esk3_2(X10,X15),u1_struct_0(X10))|(~m1_subset_1(X15,u1_struct_0(X10))|~r2_lattice3(X10,esk2_1(X10),X15))|v3_lattice3(X10)|~l1_orders_2(X10))&((r2_lattice3(X10,esk2_1(X10),esk3_2(X10,X15))|(~m1_subset_1(X15,u1_struct_0(X10))|~r2_lattice3(X10,esk2_1(X10),X15))|v3_lattice3(X10)|~l1_orders_2(X10))&(~r1_orders_2(X10,X15,esk3_2(X10,X15))|(~m1_subset_1(X15,u1_struct_0(X10))|~r2_lattice3(X10,esk2_1(X10),X15))|v3_lattice3(X10)|~l1_orders_2(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_lattice3])])])])])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (u1_struct_0(esk5_0)=X1|g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))!=g1_orders_2(X1,X2)), inference(spm,[status(thm)],[c_0_14, c_0_11]), ['final']).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (g1_orders_2(u1_struct_0(esk4_0),u1_orders_2(esk5_0))=g1_orders_2(u1_struct_0(esk5_0),u1_orders_2(esk5_0))), inference(rw,[status(thm)],[c_0_13, c_0_15])).
% 0.12/0.37  cnf(c_0_19, plain, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(X1))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v3_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.37  cnf(c_0_22, plain, (r1_orders_2(X2,esk1_2(X2,X3),X1)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_lattice3(X2,X3,X1)|~v3_lattice3(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),X2)|~r2_lattice3(esk4_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_20]), c_0_21])]), ['final']).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_24, c_0_23]), ['final']).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X2))|~r2_lattice3(esk4_0,X1,esk1_2(esk4_0,X2))), inference(spm,[status(thm)],[c_0_25, c_0_26]), ['final']).
% 0.12/0.37  cnf(c_0_28, plain, (r2_lattice3(X1,X2,esk1_2(X1,X2))|~v3_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_29, plain, (r2_lattice3(X1,esk2_1(X1),esk3_2(X1,X2))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_30, plain, (m1_subset_1(esk3_2(X1,X2),u1_struct_0(X1))|v3_lattice3(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_31, plain, (v3_lattice3(X1)|~r1_orders_2(X1,X2,esk3_2(X1,X2))|~m1_subset_1(X2,u1_struct_0(X1))|~r2_lattice3(X1,esk2_1(X1),X2)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16]), ['final']).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (~v3_lattice3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (r1_orders_2(esk4_0,esk1_2(esk4_0,X1),esk1_2(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_20]), c_0_21])]), ['final']).
% 0.12/0.37  # SZS output end Saturation
% 0.12/0.37  # Proof object total steps             : 34
% 0.12/0.37  # Proof object clause steps            : 25
% 0.12/0.37  # Proof object formula steps           : 9
% 0.12/0.37  # Proof object conjectures             : 19
% 0.12/0.37  # Proof object clause conjectures      : 16
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 14
% 0.12/0.37  # Proof object initial formulas used   : 4
% 0.12/0.37  # Proof object generating inferences   : 9
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Parsed axioms                        : 4
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 14
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 14
% 0.12/0.37  # Processed clauses                    : 42
% 0.12/0.37  # ...of these trivial                  : 2
% 0.12/0.37  # ...subsumed                          : 1
% 0.12/0.37  # ...remaining for further processing  : 39
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 3
% 0.12/0.37  # Generated clauses                    : 18
% 0.12/0.37  # ...of the previous two non-trivial   : 15
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 16
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 22
% 0.12/0.37  #    Positive orientable unit clauses  : 8
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 13
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 17
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 22
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 4
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1515
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
