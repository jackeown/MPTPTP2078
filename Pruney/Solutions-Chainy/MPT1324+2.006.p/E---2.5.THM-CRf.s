%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   24 (  43 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 161 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t45_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))
               => r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tops_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t44_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
               => ( r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))
                 => r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t45_tops_2])).

fof(c_0_4,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_5,plain,(
    ! [X10,X11,X12] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
      | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X10,X11)),k1_tops_2(X10,X11,X12)),k5_setfam_1(u1_struct_0(X10),X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_2])])])).

fof(c_0_6,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))
    & ~ r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_7,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_9,plain,
    ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,X2)),k5_setfam_1(u1_struct_0(esk2_0),X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X4,X3)
    | ~ r1_tarski(X1,X4) ),
    inference(spm,[status(thm)],[c_0_7,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))
    | ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:58:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S041A
% 0.12/0.37  # and selection function PSelectMaxLComplex.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.026 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t45_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))=>r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_tops_2)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t44_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_2)).
% 0.12/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)))=>r1_tarski(X2,k5_setfam_1(u1_struct_0(X1),X3))))))), inference(assume_negation,[status(cth)],[t45_tops_2])).
% 0.12/0.37  fof(c_0_4, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_5, plain, ![X10, X11, X12]:(~l1_pre_topc(X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X10,X11)),k1_tops_2(X10,X11,X12)),k5_setfam_1(u1_struct_0(X10),X12))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_2])])])).
% 0.12/0.37  fof(c_0_6, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))&~r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).
% 0.12/0.37  cnf(c_0_7, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_8, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_9, plain, (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X1,X2)),k1_tops_2(X1,X2,X3)),k5_setfam_1(u1_struct_0(X1),X3))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,X2)),k5_setfam_1(u1_struct_0(esk2_0),X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X4,X3)|~r1_tarski(X1,X4)), inference(spm,[status(thm)],[c_0_7, c_0_11])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,X1)),k1_tops_2(esk2_0,X1,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)),k5_setfam_1(u1_struct_0(esk2_0),esk4_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (r1_tarski(X1,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))|~r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(k1_pre_topc(esk2_0,esk3_0)),k1_tops_2(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (~r1_tarski(esk3_0,k5_setfam_1(u1_struct_0(esk2_0),esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 24
% 0.12/0.37  # Proof object clause steps            : 17
% 0.12/0.37  # Proof object formula steps           : 7
% 0.12/0.37  # Proof object conjectures             : 13
% 0.12/0.37  # Proof object clause conjectures      : 10
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 3
% 0.12/0.37  # Proof object generating inferences   : 8
% 0.12/0.37  # Proof object simplifying inferences  : 1
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 3
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 9
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 9
% 0.12/0.37  # Processed clauses                    : 35
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 3
% 0.12/0.37  # ...remaining for further processing  : 32
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 29
% 0.12/0.37  # ...of the previous two non-trivial   : 24
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 29
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
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
% 0.12/0.37  # Current number of processed clauses  : 23
% 0.12/0.37  #    Positive orientable unit clauses  : 6
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 16
% 0.12/0.37  # Current number of unprocessed clauses: 7
% 0.12/0.37  # ...number of literals in the above   : 31
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 9
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 141
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 94
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 2
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 5
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 1339
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.026 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.031 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
