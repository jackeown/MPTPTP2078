%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:15 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 169 expanded)
%              Number of clauses        :   24 (  75 expanded)
%              Number of leaves         :    3 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  102 ( 645 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t24_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_3,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_4,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

cnf(c_0_5,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v13_waybel_0(X2,X1)
            <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_0])).

cnf(c_0_7,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_4,c_0_5]),
    [final]).

fof(c_0_8,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v13_waybel_0(esk3_0,esk2_0)
      | ~ r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) )
    & ( v13_waybel_0(esk3_0,esk2_0)
      | r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_4,c_0_7]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r2_hidden(esk1_2(X1,X2),esk3_0)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk3_0,X3) ),
    inference(spm,[status(thm)],[c_0_4,c_0_11]),
    [final]).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_3]),
    [final]).

fof(c_0_14,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_15,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk3_0,X4)
    | ~ r1_tarski(X4,X3) ),
    inference(spm,[status(thm)],[c_0_4,c_0_12]),
    [final]).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_5]),
    [final]).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_19,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r2_hidden(esk1_2(k4_waybel_0(esk2_0,esk3_0),X1),X2)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)
    | ~ r1_tarski(esk3_0,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r2_hidden(esk1_2(k4_waybel_0(esk2_0,esk3_0),X1),X2)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)
    | ~ r1_tarski(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))
    | ~ r1_tarski(esk3_0,X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_12]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | m1_subset_1(esk1_2(k4_waybel_0(esk2_0,esk3_0),X1),u1_struct_0(esk2_0))
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16])]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | m1_subset_1(esk1_2(X1,X2),u1_struct_0(esk2_0))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_11]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_16]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11]),
    [final]).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk1_2(X1,X2),u1_struct_0(esk2_0))
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_7]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk1_2(esk3_0,X1),u1_struct_0(esk2_0))
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_5]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( ~ v13_waybel_0(esk3_0,esk2_0)
    | ~ r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:46:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.36  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S033N
% 0.19/0.36  # and selection function PSelectUnlessUniqMax.
% 0.19/0.36  #
% 0.19/0.36  # Preprocessing time       : 0.019 s
% 0.19/0.36  # Presaturation interreduction done
% 0.19/0.36  
% 0.19/0.36  # No proof found!
% 0.19/0.36  # SZS status CounterSatisfiable
% 0.19/0.36  # SZS output start Saturation
% 0.19/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.36  fof(t24_waybel_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>r1_tarski(k4_waybel_0(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_waybel_0)).
% 0.19/0.36  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.36  fof(c_0_3, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.36  cnf(c_0_4, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.36  cnf(c_0_5, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.36  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>r1_tarski(k4_waybel_0(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t24_waybel_0])).
% 0.19/0.36  cnf(c_0_7, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_4, c_0_5]), ['final']).
% 0.19/0.36  fof(c_0_8, negated_conjecture, (l1_orders_2(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v13_waybel_0(esk3_0,esk2_0)|~r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0))&(v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.19/0.36  cnf(c_0_9, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_4, c_0_7]), ['final']).
% 0.19/0.36  cnf(c_0_10, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.36  cnf(c_0_11, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r2_hidden(esk1_2(X1,X2),esk3_0)|r1_tarski(X1,X2)|~r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_9, c_0_10]), ['final']).
% 0.19/0.36  cnf(c_0_12, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))|~r1_tarski(esk3_0,X3)), inference(spm,[status(thm)],[c_0_4, c_0_11]), ['final']).
% 0.19/0.36  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_3]), ['final']).
% 0.19/0.36  fof(c_0_14, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|m1_subset_1(X10,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.36  cnf(c_0_15, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))|~r1_tarski(esk3_0,X4)|~r1_tarski(X4,X3)), inference(spm,[status(thm)],[c_0_4, c_0_12]), ['final']).
% 0.19/0.36  cnf(c_0_16, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_13, c_0_5]), ['final']).
% 0.19/0.36  cnf(c_0_17, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.19/0.36  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.36  cnf(c_0_19, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r2_hidden(esk1_2(k4_waybel_0(esk2_0,esk3_0),X1),X2)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)|~r1_tarski(esk3_0,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_15, c_0_16]), ['final']).
% 0.19/0.36  cnf(c_0_20, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18]), ['final']).
% 0.19/0.36  cnf(c_0_21, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r2_hidden(esk1_2(k4_waybel_0(esk2_0,esk3_0),X1),X2)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)|~r1_tarski(esk3_0,X2)), inference(spm,[status(thm)],[c_0_19, c_0_16]), ['final']).
% 0.19/0.36  cnf(c_0_22, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(X1,X2)|~r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))|~r1_tarski(esk3_0,X2)), inference(spm,[status(thm)],[c_0_13, c_0_12]), ['final']).
% 0.19/0.36  cnf(c_0_23, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|m1_subset_1(esk1_2(k4_waybel_0(esk2_0,esk3_0),X1),u1_struct_0(esk2_0))|r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_16])]), ['final']).
% 0.19/0.36  cnf(c_0_24, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|m1_subset_1(esk1_2(X1,X2),u1_struct_0(esk2_0))|r1_tarski(X1,X2)|~r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_20, c_0_11]), ['final']).
% 0.19/0.36  cnf(c_0_25, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),X1)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_22, c_0_16]), ['final']).
% 0.19/0.36  cnf(c_0_26, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(X1,esk3_0)|~r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_13, c_0_11]), ['final']).
% 0.19/0.36  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk1_2(X1,X2),u1_struct_0(esk2_0))|r1_tarski(X1,X2)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_20, c_0_7]), ['final']).
% 0.19/0.36  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk1_2(esk3_0,X1),u1_struct_0(esk2_0))|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_5]), ['final']).
% 0.19/0.36  cnf(c_0_29, negated_conjecture, (~v13_waybel_0(esk3_0,esk2_0)|~r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.36  cnf(c_0_30, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8]), ['final']).
% 0.19/0.36  # SZS output end Saturation
% 0.19/0.36  # Proof object total steps             : 31
% 0.19/0.36  # Proof object clause steps            : 24
% 0.19/0.36  # Proof object formula steps           : 7
% 0.19/0.36  # Proof object conjectures             : 20
% 0.19/0.36  # Proof object clause conjectures      : 17
% 0.19/0.36  # Proof object formula conjectures     : 3
% 0.19/0.36  # Proof object initial clauses used    : 8
% 0.19/0.36  # Proof object initial formulas used   : 3
% 0.19/0.36  # Proof object generating inferences   : 16
% 0.19/0.36  # Proof object simplifying inferences  : 2
% 0.19/0.36  # Parsed axioms                        : 3
% 0.19/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.36  # Initial clauses                      : 8
% 0.19/0.36  # Removed in clause preprocessing      : 0
% 0.19/0.36  # Initial clauses in saturation        : 8
% 0.19/0.36  # Processed clauses                    : 41
% 0.19/0.36  # ...of these trivial                  : 0
% 0.19/0.36  # ...subsumed                          : 8
% 0.19/0.36  # ...remaining for further processing  : 33
% 0.19/0.36  # Other redundant clauses eliminated   : 0
% 0.19/0.36  # Clauses deleted for lack of memory   : 0
% 0.19/0.36  # Backward-subsumed                    : 1
% 0.19/0.36  # Backward-rewritten                   : 0
% 0.19/0.36  # Generated clauses                    : 28
% 0.19/0.36  # ...of the previous two non-trivial   : 25
% 0.19/0.36  # Contextual simplify-reflections      : 0
% 0.19/0.36  # Paramodulations                      : 28
% 0.19/0.36  # Factorizations                       : 0
% 0.19/0.36  # Equation resolutions                 : 0
% 0.19/0.36  # Propositional unsat checks           : 0
% 0.19/0.36  #    Propositional check models        : 0
% 0.19/0.36  #    Propositional check unsatisfiable : 0
% 0.19/0.36  #    Propositional clauses             : 0
% 0.19/0.36  #    Propositional clauses after purity: 0
% 0.19/0.36  #    Propositional unsat core size     : 0
% 0.19/0.36  #    Propositional preprocessing time  : 0.000
% 0.19/0.36  #    Propositional encoding time       : 0.000
% 0.19/0.36  #    Propositional solver time         : 0.000
% 0.19/0.36  #    Success case prop preproc time    : 0.000
% 0.19/0.36  #    Success case prop encoding time   : 0.000
% 0.19/0.36  #    Success case prop solver time     : 0.000
% 0.19/0.36  # Current number of processed clauses  : 24
% 0.19/0.36  #    Positive orientable unit clauses  : 3
% 0.19/0.36  #    Positive unorientable unit clauses: 0
% 0.19/0.36  #    Negative unit clauses             : 0
% 0.19/0.36  #    Non-unit-clauses                  : 21
% 0.19/0.36  # Current number of unprocessed clauses: 0
% 0.19/0.36  # ...number of literals in the above   : 0
% 0.19/0.36  # Current number of archived formulas  : 0
% 0.19/0.36  # Current number of archived clauses   : 9
% 0.19/0.36  # Clause-clause subsumption calls (NU) : 224
% 0.19/0.36  # Rec. Clause-clause subsumption calls : 113
% 0.19/0.36  # Non-unit clause-clause subsumptions  : 9
% 0.19/0.36  # Unit Clause-clause subsumption calls : 3
% 0.19/0.36  # Rewrite failures with RHS unbound    : 0
% 0.19/0.36  # BW rewrite match attempts            : 3
% 0.19/0.36  # BW rewrite match successes           : 0
% 0.19/0.36  # Condensation attempts                : 0
% 0.19/0.36  # Condensation successes               : 0
% 0.19/0.36  # Termbank termtop insertions          : 1162
% 0.19/0.36  
% 0.19/0.36  # -------------------------------------------------
% 0.19/0.36  # User time                : 0.017 s
% 0.19/0.36  # System time              : 0.006 s
% 0.19/0.36  # Total time               : 0.023 s
% 0.19/0.36  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
