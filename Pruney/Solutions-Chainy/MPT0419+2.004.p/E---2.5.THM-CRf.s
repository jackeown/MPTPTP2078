%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:44 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 (  94 expanded)
%              Number of clauses        :   21 (  35 expanded)
%              Number of leaves         :    4 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   98 ( 351 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_setfam_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

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

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
             => r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_setfam_1])).

fof(c_0_5,plain,(
    ! [X11,X12,X13] :
      ( ( m1_subset_1(esk2_3(X11,X12,X13),X11)
        | r1_tarski(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X12)
        | r1_tarski(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) )
      & ( ~ r2_hidden(esk2_3(X11,X12,X13),X13)
        | r1_tarski(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_6,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0))
    & ~ r1_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17] :
      ( ( ~ r2_hidden(k3_subset_1(X15,X17),k7_setfam_1(X15,X16))
        | r2_hidden(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( ~ r2_hidden(X17,X16)
        | r2_hidden(k3_subset_1(X15,X17),k7_setfam_1(X15,X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_3(k1_zfmisc_1(esk3_0),X1,esk5_0),k1_zfmisc_1(esk3_0))
    | r1_tarski(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,X1),k7_setfam_1(esk3_0,esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),k1_zfmisc_1(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_11]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),X1,esk5_0),X1)
    | r1_tarski(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_9])).

fof(c_0_18,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),k7_setfam_1(esk3_0,esk4_0))
    | ~ r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_11]),c_0_13])).

cnf(c_0_21,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),k7_setfam_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),X1)
    | ~ r1_tarski(k7_setfam_1(esk3_0,esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r2_hidden(X2,X3)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),k7_setfam_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_9]),c_0_16])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_9]),c_0_11])]),c_0_13]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02CA
% 0.14/0.38  # and selection function SelectAntiRROptimalLit.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t51_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 0.14/0.38  fof(t7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(![X4]:(m1_subset_1(X4,X1)=>(r2_hidden(X4,X2)=>r2_hidden(X4,X3)))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 0.14/0.38  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 0.14/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t51_setfam_1])).
% 0.14/0.38  fof(c_0_5, plain, ![X11, X12, X13]:((m1_subset_1(esk2_3(X11,X12,X13),X11)|r1_tarski(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(X11)))&((r2_hidden(esk2_3(X11,X12,X13),X12)|r1_tarski(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(X11)))&(~r2_hidden(esk2_3(X11,X12,X13),X13)|r1_tarski(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X11))|~m1_subset_1(X12,k1_zfmisc_1(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).
% 0.14/0.38  fof(c_0_6, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0))&~r1_tarski(esk4_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X15, X16, X17]:((~r2_hidden(k3_subset_1(X15,X17),k7_setfam_1(X15,X16))|r2_hidden(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))&(~r2_hidden(X17,X16)|r2_hidden(k3_subset_1(X15,X17),k7_setfam_1(X15,X16))|~m1_subset_1(X17,k1_zfmisc_1(X15))|~m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 0.14/0.38  cnf(c_0_8, plain, (m1_subset_1(esk2_3(X1,X2,X3),X1)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, plain, (r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk2_3(k1_zfmisc_1(esk3_0),X1,esk5_0),k1_zfmisc_1(esk3_0))|r1_tarski(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.38  cnf(c_0_13, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_14, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_tarski(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,X1),k7_setfam_1(esk3_0,esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),k1_zfmisc_1(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_11]), c_0_13])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),X1,esk5_0),X1)|r1_tarski(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(spm,[status(thm)],[c_0_14, c_0_9])).
% 0.14/0.38  fof(c_0_18, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),k7_setfam_1(esk3_0,esk4_0))|~r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_11]), c_0_13])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),k7_setfam_1(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.14/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),X1)|~r1_tarski(k7_setfam_1(esk3_0,esk4_0),X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(X2,X3)|~r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0)),k7_setfam_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.38  cnf(c_0_27, plain, (r1_tarski(X2,X3)|~r2_hidden(esk2_3(X1,X2,X3),X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_3(k1_zfmisc_1(esk3_0),esk4_0,esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_9]), c_0_16])])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_9]), c_0_11])]), c_0_13]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 30
% 0.14/0.38  # Proof object clause steps            : 21
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 18
% 0.14/0.38  # Proof object clause conjectures      : 15
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 10
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 10
% 0.14/0.38  # Proof object simplifying inferences  : 11
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 12
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 12
% 0.14/0.38  # Processed clauses                    : 68
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 6
% 0.14/0.38  # ...remaining for further processing  : 62
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 2
% 0.14/0.38  # Generated clauses                    : 102
% 0.14/0.38  # ...of the previous two non-trivial   : 72
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 96
% 0.14/0.38  # Factorizations                       : 6
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 48
% 0.14/0.38  #    Positive orientable unit clauses  : 9
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 38
% 0.14/0.38  # Current number of unprocessed clauses: 27
% 0.14/0.38  # ...number of literals in the above   : 90
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 14
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 221
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 162
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 6
% 0.14/0.38  # Unit Clause-clause subsumption calls : 2
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 2
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2929
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.032 s
% 0.14/0.38  # System time              : 0.002 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
