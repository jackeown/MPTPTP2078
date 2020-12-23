%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:44 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  89 expanded)
%              Number of clauses        :   26 (  41 expanded)
%              Number of leaves         :    5 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 307 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t49_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))
          <=> r2_hidden(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
           => ( r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))
             => r1_tarski(X2,X3) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_setfam_1])).

fof(c_0_6,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_7,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    & r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0))
    & ~ r1_tarski(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | r1_tarski(X12,X10)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r1_tarski(X13,X10)
        | r2_hidden(X13,X11)
        | X11 != k1_zfmisc_1(X10) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | ~ r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) )
      & ( r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(esk2_2(X14,X15),X14)
        | X15 = k1_zfmisc_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(X1,k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),k1_zfmisc_1(esk3_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r2_hidden(k3_subset_1(X19,X21),k7_setfam_1(X19,X20))
        | r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) )
      & ( ~ r2_hidden(X21,X20)
        | r2_hidden(k3_subset_1(X19,X21),k7_setfam_1(X19,X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(X19))
        | ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_2(esk4_0,X1),esk3_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,plain,
    ( r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk3_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_24,plain,
    ( r2_hidden(X2,X3)
    | ~ r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,X2))
    | r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ r2_hidden(esk1_2(esk4_0,X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),X2)
    | r1_tarski(esk4_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))
    | ~ r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,X2)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,k7_setfam_1(esk3_0,esk5_0))
    | ~ r2_hidden(X1,k7_setfam_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,esk4_0))
    | r1_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_10]),c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk5_0)
    | r1_tarski(esk4_0,X1)
    | ~ r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,esk5_0))
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,X1),esk5_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( ~ r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___024_B31_F1_PI_AE_Q4_CS_SP_S2S
% 0.20/0.42  # and selection function SelectNewComplexAHP.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.049 s
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(t51_setfam_1, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 0.20/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.42  fof(t49_setfam_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>(r2_hidden(k3_subset_1(X1,X3),k7_setfam_1(X1,X2))<=>r2_hidden(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 0.20/0.42  fof(c_0_5, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(r1_tarski(k7_setfam_1(X1,X2),k7_setfam_1(X1,X3))=>r1_tarski(X2,X3))))), inference(assume_negation,[status(cth)],[t51_setfam_1])).
% 0.20/0.42  fof(c_0_6, plain, ![X17, X18]:((~m1_subset_1(X17,k1_zfmisc_1(X18))|r1_tarski(X17,X18))&(~r1_tarski(X17,X18)|m1_subset_1(X17,k1_zfmisc_1(X18)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.42  fof(c_0_7, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))&(r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0))&~r1_tarski(esk4_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.20/0.42  fof(c_0_8, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  fof(c_0_11, plain, ![X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X12,X11)|r1_tarski(X12,X10)|X11!=k1_zfmisc_1(X10))&(~r1_tarski(X13,X10)|r2_hidden(X13,X11)|X11!=k1_zfmisc_1(X10)))&((~r2_hidden(esk2_2(X14,X15),X15)|~r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14))&(r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(esk2_2(X14,X15),X14)|X15=k1_zfmisc_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.42  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_13, negated_conjecture, (r1_tarski(esk4_0,k1_zfmisc_1(esk3_0))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.42  cnf(c_0_14, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.42  cnf(c_0_15, negated_conjecture, (r2_hidden(X1,k1_zfmisc_1(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.42  cnf(c_0_16, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),k1_zfmisc_1(esk3_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.42  fof(c_0_19, plain, ![X19, X20, X21]:((~r2_hidden(k3_subset_1(X19,X21),k7_setfam_1(X19,X20))|r2_hidden(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))&(~r2_hidden(X21,X20)|r2_hidden(k3_subset_1(X19,X21),k7_setfam_1(X19,X20))|~m1_subset_1(X21,k1_zfmisc_1(X19))|~m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t49_setfam_1])])])])).
% 0.20/0.42  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_21, negated_conjecture, (r1_tarski(esk1_2(esk4_0,X1),esk3_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.42  cnf(c_0_22, plain, (r2_hidden(k3_subset_1(X3,X1),k7_setfam_1(X3,X2))|~r2_hidden(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,X1),k1_zfmisc_1(esk3_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.42  cnf(c_0_24, plain, (r2_hidden(X2,X3)|~r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.42  cnf(c_0_25, negated_conjecture, (r1_tarski(k7_setfam_1(esk3_0,esk4_0),k7_setfam_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,X2))|r1_tarski(esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~r2_hidden(esk1_2(esk4_0,X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.42  cnf(c_0_27, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),X2)|r1_tarski(esk4_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))|~r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,X2))), inference(spm,[status(thm)],[c_0_24, c_0_23])).
% 0.20/0.42  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,k7_setfam_1(esk3_0,esk5_0))|~r2_hidden(X1,k7_setfam_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_12, c_0_25])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,esk4_0))|r1_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_10]), c_0_16])).
% 0.20/0.42  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r1_tarski(esk4_0,X1)|~r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.42  cnf(c_0_32, negated_conjecture, (r2_hidden(k3_subset_1(esk3_0,esk1_2(esk4_0,X1)),k7_setfam_1(esk3_0,esk5_0))|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.42  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk4_0,X1),esk5_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, (~r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_36, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 37
% 0.20/0.42  # Proof object clause steps            : 26
% 0.20/0.42  # Proof object formula steps           : 11
% 0.20/0.42  # Proof object conjectures             : 20
% 0.20/0.42  # Proof object clause conjectures      : 17
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 12
% 0.20/0.42  # Proof object initial formulas used   : 5
% 0.20/0.42  # Proof object generating inferences   : 14
% 0.20/0.42  # Proof object simplifying inferences  : 2
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 5
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 15
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 15
% 0.20/0.42  # Processed clauses                    : 203
% 0.20/0.42  # ...of these trivial                  : 0
% 0.20/0.42  # ...subsumed                          : 49
% 0.20/0.42  # ...remaining for further processing  : 154
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 2
% 0.20/0.42  # Backward-rewritten                   : 1
% 0.20/0.42  # Generated clauses                    : 480
% 0.20/0.42  # ...of the previous two non-trivial   : 458
% 0.20/0.42  # Contextual simplify-reflections      : 3
% 0.20/0.42  # Paramodulations                      : 468
% 0.20/0.42  # Factorizations                       : 10
% 0.20/0.42  # Equation resolutions                 : 2
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 151
% 0.20/0.42  #    Positive orientable unit clauses  : 20
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 130
% 0.20/0.42  # Current number of unprocessed clauses: 269
% 0.20/0.42  # ...number of literals in the above   : 1222
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 3
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 1071
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 579
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 54
% 0.20/0.42  # Unit Clause-clause subsumption calls : 18
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 21
% 0.20/0.42  # BW rewrite match successes           : 1
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 11621
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.076 s
% 0.20/0.42  # System time              : 0.005 s
% 0.20/0.42  # Total time               : 0.081 s
% 0.20/0.42  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
