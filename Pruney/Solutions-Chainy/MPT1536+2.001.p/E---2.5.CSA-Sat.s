%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:14 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 557 expanded)
%              Number of clauses        :   26 ( 230 expanded)
%              Number of leaves         :    4 ( 130 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 (2584 expanded)
%              Number of equality atoms :   30 ( 646 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_orders_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3,X4] :
          ( g1_orders_2(X1,X2) = g1_orders_2(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(t14_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( l1_orders_2(X2)
         => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
           => ! [X3] :
                ( ( r1_yellow_0(X1,X3)
                 => r1_yellow_0(X2,X3) )
                & ( r2_yellow_0(X1,X3)
                 => r2_yellow_0(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_0)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(c_0_4,plain,(
    ! [X9,X10,X11,X12] :
      ( ( X9 = X11
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) )
      & ( X10 = X12
        | g1_orders_2(X9,X10) != g1_orders_2(X11,X12)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).

fof(c_0_5,plain,(
    ! [X8] :
      ( ~ l1_orders_2(X8)
      | m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( l1_orders_2(X2)
           => ( g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
             => ! [X3] :
                  ( ( r1_yellow_0(X1,X3)
                   => r1_yellow_0(X2,X3) )
                  & ( r2_yellow_0(X1,X3)
                   => r2_yellow_0(X2,X3) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_yellow_0])).

cnf(c_0_7,plain,
    ( X1 = X2
    | g1_orders_2(X3,X1) != g1_orders_2(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_8,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

fof(c_0_9,negated_conjecture,
    ( l1_orders_2(esk1_0)
    & l1_orders_2(esk2_0)
    & g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))
    & ( r2_yellow_0(esk1_0,esk3_0)
      | r1_yellow_0(esk1_0,esk3_0) )
    & ( ~ r2_yellow_0(esk2_0,esk3_0)
      | r1_yellow_0(esk1_0,esk3_0) )
    & ( r2_yellow_0(esk1_0,esk3_0)
      | ~ r1_yellow_0(esk2_0,esk3_0) )
    & ( ~ r2_yellow_0(esk2_0,esk3_0)
      | ~ r1_yellow_0(esk2_0,esk3_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_10,plain,
    ( u1_orders_2(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X3,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( u1_orders_2(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])])).

cnf(c_0_14,plain,
    ( X1 = X2
    | g1_orders_2(X1,X3) != g1_orders_2(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_15,negated_conjecture,
    ( u1_orders_2(esk1_0) = u1_orders_2(esk2_0) ),
    inference(er,[status(thm)],[c_0_13]),
    [final]).

cnf(c_0_16,plain,
    ( u1_struct_0(X1) = X2
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(X2,X3)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_8]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk2_0)) = g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_11,c_0_15])).

fof(c_0_18,plain,(
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

cnf(c_0_19,negated_conjecture,
    ( u1_struct_0(esk1_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_15]),c_0_17]),c_0_12])])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(er,[status(thm)],[c_0_19]),
    [final]).

cnf(c_0_22,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk2_0))
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_15]),c_0_12])]),c_0_21]),c_0_21]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_15]),c_0_12])]),c_0_21]),c_0_21]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,X2)
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,X2)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_20]),c_0_24])]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_21]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( u1_orders_2(esk2_0) = X1
    | g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0)) != g1_orders_2(X2,X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_15]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | r1_yellow_0(esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | ~ r1_yellow_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0)
    | ~ r2_yellow_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_yellow_0(esk2_0,esk3_0)
    | ~ r1_yellow_0(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_15]),c_0_12])]),c_0_21]),c_0_21]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:57:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.027 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # No proof found!
% 0.20/0.38  # SZS status CounterSatisfiable
% 0.20/0.38  # SZS output start Saturation
% 0.20/0.38  fof(free_g1_orders_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3, X4]:(g1_orders_2(X1,X2)=g1_orders_2(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_orders_2)).
% 0.20/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.20/0.38  fof(t14_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:((r1_yellow_0(X1,X3)=>r1_yellow_0(X2,X3))&(r2_yellow_0(X1,X3)=>r2_yellow_0(X2,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_0)).
% 0.20/0.38  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.20/0.38  fof(c_0_4, plain, ![X9, X10, X11, X12]:((X9=X11|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))&(X10=X12|g1_orders_2(X9,X10)!=g1_orders_2(X11,X12)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_orders_2])])])])).
% 0.20/0.38  fof(c_0_5, plain, ![X8]:(~l1_orders_2(X8)|m1_subset_1(u1_orders_2(X8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X8))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.20/0.38  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(l1_orders_2(X2)=>(g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))=g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))=>![X3]:((r1_yellow_0(X1,X3)=>r1_yellow_0(X2,X3))&(r2_yellow_0(X1,X3)=>r2_yellow_0(X2,X3))))))), inference(assume_negation,[status(cth)],[t14_yellow_0])).
% 0.20/0.38  cnf(c_0_7, plain, (X1=X2|g1_orders_2(X3,X1)!=g1_orders_2(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.38  cnf(c_0_8, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.38  fof(c_0_9, negated_conjecture, (l1_orders_2(esk1_0)&(l1_orders_2(esk2_0)&(g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))&(((r2_yellow_0(esk1_0,esk3_0)|r1_yellow_0(esk1_0,esk3_0))&(~r2_yellow_0(esk2_0,esk3_0)|r1_yellow_0(esk1_0,esk3_0)))&((r2_yellow_0(esk1_0,esk3_0)|~r1_yellow_0(esk2_0,esk3_0))&(~r2_yellow_0(esk2_0,esk3_0)|~r1_yellow_0(esk2_0,esk3_0))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.20/0.38  cnf(c_0_10, plain, (u1_orders_2(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X3,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_7, c_0_8]), ['final']).
% 0.20/0.38  cnf(c_0_11, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk1_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_12, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_13, negated_conjecture, (u1_orders_2(esk1_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])])).
% 0.20/0.38  cnf(c_0_14, plain, (X1=X2|g1_orders_2(X1,X3)!=g1_orders_2(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.38  cnf(c_0_15, negated_conjecture, (u1_orders_2(esk1_0)=u1_orders_2(esk2_0)), inference(er,[status(thm)],[c_0_13]), ['final']).
% 0.20/0.38  cnf(c_0_16, plain, (u1_struct_0(X1)=X2|g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))!=g1_orders_2(X2,X3)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_14, c_0_8]), ['final']).
% 0.20/0.38  cnf(c_0_17, negated_conjecture, (g1_orders_2(u1_struct_0(esk1_0),u1_orders_2(esk2_0))=g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))), inference(rw,[status(thm)],[c_0_11, c_0_15])).
% 0.20/0.38  fof(c_0_18, plain, ![X5, X6, X7]:((~r1_orders_2(X5,X6,X7)|r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))&(~r2_hidden(k4_tarski(X6,X7),u1_orders_2(X5))|r1_orders_2(X5,X6,X7)|~m1_subset_1(X7,u1_struct_0(X5))|~m1_subset_1(X6,u1_struct_0(X5))|~l1_orders_2(X5))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (u1_struct_0(esk1_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_15]), c_0_17]), c_0_12])])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))|~r1_orders_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (u1_struct_0(esk1_0)=u1_struct_0(esk2_0)), inference(er,[status(thm)],[c_0_19]), ['final']).
% 0.20/0.38  cnf(c_0_22, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_18]), ['final']).
% 0.20/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk2_0))|~r1_orders_2(esk1_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_15]), c_0_12])]), c_0_21]), c_0_21]), ['final']).
% 0.20/0.38  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_25, negated_conjecture, (r1_orders_2(esk1_0,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk2_0))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_15]), c_0_12])]), c_0_21]), c_0_21]), ['final']).
% 0.20/0.38  cnf(c_0_26, negated_conjecture, (r1_orders_2(esk2_0,X1,X2)|~r1_orders_2(esk1_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])]), ['final']).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk1_0,X1,X2)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_20]), c_0_24])]), ['final']).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (u1_struct_0(esk2_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_21]), ['final']).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (u1_orders_2(esk2_0)=X1|g1_orders_2(u1_struct_0(esk2_0),u1_orders_2(esk2_0))!=g1_orders_2(X2,X1)), inference(rw,[status(thm)],[c_0_13, c_0_15]), ['final']).
% 0.20/0.38  cnf(c_0_30, negated_conjecture, (r2_yellow_0(esk1_0,esk3_0)|r1_yellow_0(esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_31, negated_conjecture, (r2_yellow_0(esk1_0,esk3_0)|~r1_yellow_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (r1_yellow_0(esk1_0,esk3_0)|~r2_yellow_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_33, negated_conjecture, (~r2_yellow_0(esk2_0,esk3_0)|~r1_yellow_0(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9]), ['final']).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, (m1_subset_1(u1_orders_2(esk2_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_15]), c_0_12])]), c_0_21]), c_0_21]), ['final']).
% 0.20/0.38  # SZS output end Saturation
% 0.20/0.38  # Proof object total steps             : 35
% 0.20/0.38  # Proof object clause steps            : 26
% 0.20/0.38  # Proof object formula steps           : 9
% 0.20/0.38  # Proof object conjectures             : 22
% 0.20/0.38  # Proof object clause conjectures      : 19
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 12
% 0.20/0.38  # Proof object initial formulas used   : 4
% 0.20/0.38  # Proof object generating inferences   : 11
% 0.20/0.38  # Proof object simplifying inferences  : 24
% 0.20/0.38  # Parsed axioms                        : 4
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 12
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 12
% 0.20/0.38  # Processed clauses                    : 44
% 0.20/0.38  # ...of these trivial                  : 1
% 0.20/0.38  # ...subsumed                          : 5
% 0.20/0.38  # ...remaining for further processing  : 38
% 0.20/0.38  # Other redundant clauses eliminated   : 0
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 4
% 0.20/0.38  # Generated clauses                    : 27
% 0.20/0.38  # ...of the previous two non-trivial   : 23
% 0.20/0.38  # Contextual simplify-reflections      : 0
% 0.20/0.38  # Paramodulations                      : 21
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 6
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 22
% 0.20/0.38  #    Positive orientable unit clauses  : 5
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 17
% 0.20/0.38  # Current number of unprocessed clauses: 0
% 0.20/0.38  # ...number of literals in the above   : 0
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 16
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 18
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 9
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.20/0.38  # Unit Clause-clause subsumption calls : 0
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 2
% 0.20/0.38  # BW rewrite match successes           : 2
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 1423
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.029 s
% 0.20/0.38  # System time              : 0.003 s
% 0.20/0.38  # Total time               : 0.032 s
% 0.20/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
