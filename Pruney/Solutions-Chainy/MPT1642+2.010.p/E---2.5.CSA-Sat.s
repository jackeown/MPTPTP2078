%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:14 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  75 expanded)
%              Number of clauses        :   15 (  24 expanded)
%              Number of leaves         :    3 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  100 ( 447 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t22_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
               => r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r1_orders_2(X1,X2,X3)
                 => r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t22_waybel_0])).

fof(c_0_4,plain,(
    ! [X9,X10,X11,X12] :
      ( ~ v4_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ r1_orders_2(X9,X10,X11)
      | ~ r1_orders_2(X9,X11,X12)
      | r1_orders_2(X9,X10,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).

fof(c_0_5,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v4_orders_2(esk2_0)
    & l1_orders_2(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & r1_orders_2(esk2_0,esk3_0,esk4_0)
    & ~ r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

cnf(c_0_6,plain,
    ( r1_orders_2(X1,X2,X4)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ r1_orders_2(X1,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_4]),
    [final]).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_8,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_9,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_10,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9])]),
    [final]).

cnf(c_0_11,negated_conjecture,
    ( r1_orders_2(esk2_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_13,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12])]),
    [final]).

fof(c_0_14,plain,(
    ! [X5,X6,X7] :
      ( ( m1_subset_1(esk1_3(X5,X6,X7),X5)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X6)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) )
      & ( ~ r2_hidden(esk1_3(X5,X6,X7),X7)
        | r1_tarski(X6,X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
        | ~ m1_subset_1(X6,k1_zfmisc_1(X5)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_15,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk4_0)
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_13]),
    [final]).

cnf(c_0_16,negated_conjecture,
    ( r1_orders_2(esk2_0,X1,esk3_0)
    | ~ r1_orders_2(esk2_0,X2,esk3_0)
    | ~ r1_orders_2(esk2_0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_12]),c_0_8]),c_0_9])]),
    [final]).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_18,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14]),
    [final]).

cnf(c_0_20,negated_conjecture,
    ( ~ r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5]),
    [final]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:37:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.026 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # No proof found!
% 0.20/0.37  # SZS status CounterSatisfiable
% 0.20/0.37  # SZS output start Saturation
% 0.20/0.37  fof(t22_waybel_0, conjecture, ![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_0)).
% 0.20/0.37  fof(t26_orders_2, axiom, ![X1]:((v4_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X3)&r1_orders_2(X1,X3,X4))=>r1_orders_2(X1,X2,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 0.20/0.37  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 0.20/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v4_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)=>r1_tarski(k6_waybel_0(X1,X3),k6_waybel_0(X1,X2))))))), inference(assume_negation,[status(cth)],[t22_waybel_0])).
% 0.20/0.37  fof(c_0_4, plain, ![X9, X10, X11, X12]:(~v4_orders_2(X9)|~l1_orders_2(X9)|(~m1_subset_1(X10,u1_struct_0(X9))|(~m1_subset_1(X11,u1_struct_0(X9))|(~m1_subset_1(X12,u1_struct_0(X9))|(~r1_orders_2(X9,X10,X11)|~r1_orders_2(X9,X11,X12)|r1_orders_2(X9,X10,X12)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_orders_2])])])).
% 0.20/0.37  fof(c_0_5, negated_conjecture, (((~v2_struct_0(esk2_0)&v4_orders_2(esk2_0))&l1_orders_2(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,u1_struct_0(esk2_0))&(r1_orders_2(esk2_0,esk3_0,esk4_0)&~r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).
% 0.20/0.37  cnf(c_0_6, plain, (r1_orders_2(X1,X2,X4)|~v4_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~r1_orders_2(X1,X2,X3)|~r1_orders_2(X1,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_4]), ['final']).
% 0.20/0.37  cnf(c_0_7, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_8, negated_conjecture, (l1_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_9, negated_conjecture, (v4_orders_2(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_10, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X2,esk4_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9])]), ['final']).
% 0.20/0.37  cnf(c_0_11, negated_conjecture, (r1_orders_2(esk2_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X1,esk3_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10, c_0_11]), c_0_12])]), ['final']).
% 0.20/0.37  fof(c_0_14, plain, ![X5, X6, X7]:((m1_subset_1(esk1_3(X5,X6,X7),X5)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&((r2_hidden(esk1_3(X5,X6,X7),X6)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5)))&(~r2_hidden(esk1_3(X5,X6,X7),X7)|r1_tarski(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X5))|~m1_subset_1(X6,k1_zfmisc_1(X5))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (r1_orders_2(esk2_0,X1,esk4_0)|~r1_orders_2(esk2_0,X2,esk3_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_10, c_0_13]), ['final']).
% 0.20/0.37  cnf(c_0_16, negated_conjecture, (r1_orders_2(esk2_0,X1,esk3_0)|~r1_orders_2(esk2_0,X2,esk3_0)|~r1_orders_2(esk2_0,X1,X2)|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_12]), c_0_8]), c_0_9])]), ['final']).
% 0.20/0.37  cnf(c_0_17, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.37  cnf(c_0_18, plain, (r1_tarski(X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.37  cnf(c_0_19, plain, (m1_subset_1(esk1_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14]), ['final']).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (~r1_tarski(k6_waybel_0(esk2_0,esk4_0),k6_waybel_0(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
% 0.20/0.37  # SZS output end Saturation
% 0.20/0.37  # Proof object total steps             : 22
% 0.20/0.37  # Proof object clause steps            : 15
% 0.20/0.37  # Proof object formula steps           : 7
% 0.20/0.37  # Proof object conjectures             : 14
% 0.20/0.37  # Proof object clause conjectures      : 11
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 3
% 0.20/0.37  # Proof object generating inferences   : 4
% 0.20/0.37  # Proof object simplifying inferences  : 8
% 0.20/0.37  # Parsed axioms                        : 3
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 11
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 11
% 0.20/0.37  # Processed clauses                    : 26
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 26
% 0.20/0.37  # Other redundant clauses eliminated   : 0
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 4
% 0.20/0.37  # ...of the previous two non-trivial   : 4
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 4
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
% 0.20/0.37  # Current number of processed clauses  : 15
% 0.20/0.37  #    Positive orientable unit clauses  : 5
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 8
% 0.20/0.37  # Current number of unprocessed clauses: 0
% 0.20/0.37  # ...number of literals in the above   : 0
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 11
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 10
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 4
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 0
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1128
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.028 s
% 0.20/0.37  # System time              : 0.003 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
