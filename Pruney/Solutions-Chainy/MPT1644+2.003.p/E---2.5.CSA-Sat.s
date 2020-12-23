%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:15 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 157 expanded)
%              Number of clauses        :   27 (  65 expanded)
%              Number of leaves         :    4 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 630 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_waybel_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v13_waybel_0(X2,X1)
            <=> r1_tarski(k4_waybel_0(X1,X2),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t24_waybel_0])).

fof(c_0_5,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_6,negated_conjecture,
    ( l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v13_waybel_0(esk3_0,esk2_0)
      | ~ r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) )
    & ( v13_waybel_0(esk3_0,esk2_0)
      | r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X8,X9,X10] :
      ( ( m1_subset_1(esk1_3(X8,X9,X10),X8)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( r2_hidden(esk1_3(X8,X9,X10),X9)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) )
      & ( ~ r2_hidden(esk1_3(X8,X9,X10),X10)
        | r1_tarski(X9,X10)
        | ~ m1_subset_1(X10,k1_zfmisc_1(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11]),
    [final]).

cnf(c_0_14,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))
    | r2_hidden(esk1_3(esk3_0,X1,k4_waybel_0(esk2_0,esk3_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_12]),
    [final]).

fof(c_0_15,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_16,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0)
    | r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),k4_waybel_0(esk2_0,esk3_0))
    | r2_hidden(esk1_3(esk3_0,k4_waybel_0(esk2_0,esk3_0),k4_waybel_0(esk2_0,esk3_0)),k4_waybel_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11])]),
    [final]).

cnf(c_0_21,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7]),
    [final]).

cnf(c_0_22,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(k4_waybel_0(esk2_0,esk3_0),k4_waybel_0(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_18]),c_0_12]),
    [final]).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11]),
    [final]).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_8,c_0_20]),
    [final]).

cnf(c_0_25,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk3_0,X1,k4_waybel_0(esk2_0,esk3_0)),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_12]),
    [final]).

cnf(c_0_26,negated_conjecture,
    ( ~ v13_waybel_0(esk3_0,esk2_0)
    | ~ r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_28,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k4_waybel_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_22]),
    [final]).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(esk1_3(X2,X1,u1_struct_0(esk2_0)),esk3_0)
    | ~ m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23]),
    [final]).

cnf(c_0_30,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(esk3_0,k4_waybel_0(esk2_0,esk3_0))
    | r2_hidden(esk1_3(esk3_0,esk3_0,k4_waybel_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_24]),
    [final]).

cnf(c_0_31,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r1_tarski(esk3_0,k4_waybel_0(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk3_0,esk3_0,k4_waybel_0(esk2_0,esk3_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24]),
    [final]).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11]),
    [final]).

cnf(c_0_33,negated_conjecture,
    ( v13_waybel_0(esk3_0,esk2_0)
    | r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k4_waybel_0(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_12]),
    [final]).

cnf(c_0_34,negated_conjecture,
    ( ~ v13_waybel_0(esk3_0,esk2_0)
    | ~ m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]),
    [final]).

cnf(c_0_35,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(t24_waybel_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>r1_tarski(k4_waybel_0(X1,X2),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_waybel_0)).
% 0.20/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.37  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.20/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>r1_tarski(k4_waybel_0(X1,X2),X2))))), inference(assume_negation,[status(cth)],[t24_waybel_0])).
% 0.20/0.37  fof(c_0_5, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.37  fof(c_0_6, negated_conjecture, (l1_orders_2(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v13_waybel_0(esk3_0,esk2_0)|~r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0))&(v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.20/0.37  fof(c_0_7, plain, ![X8, X9, X10]:((m1_subset_1(esk1_3(X8,X9,X10),X8)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&((r2_hidden(esk1_3(X8,X9,X10),X9)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8)))&(~r2_hidden(esk1_3(X8,X9,X10),X10)|r1_tarski(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X8))|~m1_subset_1(X9,k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.20/0.37  cnf(c_0_8, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_9, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.37  cnf(c_0_10, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_8, c_0_9]), ['final']).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (r1_tarski(X1,esk3_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_10, c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))|r2_hidden(esk1_3(esk3_0,X1,k4_waybel_0(esk2_0,esk3_0)),X1)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_10, c_0_12]), ['final']).
% 0.20/0.37  fof(c_0_15, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.37  cnf(c_0_16, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.37  cnf(c_0_17, negated_conjecture, (r1_tarski(esk3_0,esk3_0)|r2_hidden(esk1_3(u1_struct_0(esk2_0),esk3_0,esk3_0),esk3_0)), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),k4_waybel_0(esk2_0,esk3_0))|r2_hidden(esk1_3(esk3_0,k4_waybel_0(esk2_0,esk3_0),k4_waybel_0(esk2_0,esk3_0)),k4_waybel_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_14, c_0_12])).
% 0.20/0.37  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15]), ['final']).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(esk3_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11])]), ['final']).
% 0.20/0.37  cnf(c_0_21, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7]), ['final']).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(k4_waybel_0(esk2_0,esk3_0),k4_waybel_0(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_18]), c_0_12]), ['final']).
% 0.20/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_8, c_0_20]), ['final']).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(X1,k4_waybel_0(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk3_0,X1,k4_waybel_0(esk2_0,esk3_0)),esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_21, c_0_12]), ['final']).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (~v13_waybel_0(esk3_0,esk2_0)|~r1_tarski(k4_waybel_0(esk2_0,esk3_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.37  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(k4_waybel_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_8, c_0_22]), ['final']).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk2_0))|~r2_hidden(esk1_3(X2,X1,u1_struct_0(esk2_0)),esk3_0)|~m1_subset_1(u1_struct_0(esk2_0),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_16, c_0_23]), ['final']).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(esk3_0,k4_waybel_0(esk2_0,esk3_0))|r2_hidden(esk1_3(esk3_0,esk3_0,k4_waybel_0(esk2_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_14, c_0_24]), ['final']).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r1_tarski(esk3_0,k4_waybel_0(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk3_0,esk3_0,k4_waybel_0(esk2_0,esk3_0)),esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_24]), ['final']).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (r1_tarski(X1,esk3_0)|m1_subset_1(esk1_3(u1_struct_0(esk2_0),X1,esk3_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_21, c_0_11]), ['final']).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (v13_waybel_0(esk3_0,esk2_0)|r2_hidden(X1,esk3_0)|~r2_hidden(X1,k4_waybel_0(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_19, c_0_12]), ['final']).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (~v13_waybel_0(esk3_0,esk2_0)|~m1_subset_1(k4_waybel_0(esk2_0,esk3_0),k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_26, c_0_27]), ['final']).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 36
% 0.20/0.37  # Proof object clause steps            : 27
% 0.20/0.37  # Proof object formula steps           : 9
% 0.20/0.37  # Proof object conjectures             : 24
% 0.20/0.37  # Proof object clause conjectures      : 21
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 10
% 0.20/0.37  # Proof object initial formulas used   : 4
% 0.20/0.37  # Proof object generating inferences   : 17
% 0.20/0.37  # Proof object simplifying inferences  : 3
% 0.20/0.37  # Parsed axioms                        : 4
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 10
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 10
% 0.20/0.37  # Processed clauses                    : 43
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 4
% 0.20/0.37  # ...remaining for further processing  : 39
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 2
% 0.20/0.37  # Backward-rewritten                   : 2
% 0.20/0.37  # Generated clauses                    : 29
% 0.20/0.37  # ...of the previous two non-trivial   : 24
% 0.20/0.37  # Contextual simplify-reflections      : 1
% 0.20/0.37  # Paramodulations                      : 29
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
% 0.20/0.37  # Current number of processed clauses  : 25
% 0.20/0.37  #    Positive orientable unit clauses  : 4
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 0
% 0.20/0.37  #    Non-unit-clauses                  : 21
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 14
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 80
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 60
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.20/0.37  # Unit Clause-clause subsumption calls : 5
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 1
% 0.20/0.37  # BW rewrite match successes           : 1
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1397
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.029 s
% 0.20/0.37  # System time              : 0.002 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
