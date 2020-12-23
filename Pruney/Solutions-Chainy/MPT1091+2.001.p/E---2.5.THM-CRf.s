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
% DateTime   : Thu Dec  3 11:08:28 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 176 expanded)
%              Number of clauses        :   21 (  79 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 534 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_finset_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ~ v1_finset_1(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_finset_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_finset_1])])])).

fof(c_0_8,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_9,plain,
    ( v1_finset_1(X2)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X5] : r1_tarski(X5,k1_zfmisc_1(k3_tarski(X5))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_12,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X10] :
      ( ~ v1_finset_1(X10)
      | v1_finset_1(k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_finset_1(X1)
          & ! [X2] :
              ( r2_hidden(X2,X1)
             => v1_finset_1(X2) ) )
      <=> v1_finset_1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t25_finset_1])).

cnf(c_0_16,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( v1_finset_1(k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X15] :
      ( ( r2_hidden(esk3_0,esk2_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ v1_finset_1(esk3_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( v1_finset_1(esk2_0)
        | v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ r2_hidden(X15,esk2_0)
        | v1_finset_1(X15)
        | v1_finset_1(k3_tarski(esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

cnf(c_0_19,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( v1_finset_1(esk2_0)
    | v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X3,X4] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(X3,k3_tarski(X4)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_finset_1(esk3_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X11] :
      ( ( r2_hidden(esk1_1(X11),X11)
        | ~ v1_finset_1(X11)
        | v1_finset_1(k3_tarski(X11)) )
      & ( ~ v1_finset_1(esk1_1(X11))
        | ~ v1_finset_1(X11)
        | v1_finset_1(k3_tarski(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(esk2_0))
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0))
    | ~ v1_finset_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23])])).

cnf(c_0_30,negated_conjecture,
    ( v1_finset_1(X1)
    | v1_finset_1(k3_tarski(esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(esk1_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v1_finset_1(esk1_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_23])]),c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_N___023_B07_F1_SP_PI_Q7_CS_SE_S0Y
% 0.12/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(cc2_finset_1, axiom, ![X1]:(v1_finset_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_finset_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_finset_1)).
% 0.12/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.36  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.12/0.36  fof(fc17_finset_1, axiom, ![X1]:(v1_finset_1(X1)=>v1_finset_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_finset_1)).
% 0.12/0.36  fof(t25_finset_1, conjecture, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_finset_1)).
% 0.12/0.36  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.12/0.36  fof(l22_finset_1, axiom, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l22_finset_1)).
% 0.12/0.36  fof(c_0_7, plain, ![X8, X9]:(~v1_finset_1(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_finset_1(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_finset_1])])])).
% 0.12/0.36  fof(c_0_8, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.36  cnf(c_0_9, plain, (v1_finset_1(X2)|~v1_finset_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_10, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  fof(c_0_11, plain, ![X5]:r1_tarski(X5,k1_zfmisc_1(k3_tarski(X5))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.12/0.36  cnf(c_0_12, plain, (v1_finset_1(X1)|~v1_finset_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.36  cnf(c_0_13, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.36  fof(c_0_14, plain, ![X10]:(~v1_finset_1(X10)|v1_finset_1(k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).
% 0.12/0.36  fof(c_0_15, negated_conjecture, ~(![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t25_finset_1])).
% 0.12/0.36  cnf(c_0_16, plain, (v1_finset_1(X1)|~v1_finset_1(k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.36  cnf(c_0_17, plain, (v1_finset_1(k1_zfmisc_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.36  fof(c_0_18, negated_conjecture, ![X15]:(((r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0)))&(~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))))&((v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0)))&(~r2_hidden(X15,esk2_0)|v1_finset_1(X15)|v1_finset_1(k3_tarski(esk2_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).
% 0.12/0.36  cnf(c_0_19, plain, (v1_finset_1(X1)|~v1_finset_1(k3_tarski(X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.36  cnf(c_0_20, negated_conjecture, (v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_21, plain, ![X3, X4]:(~r2_hidden(X3,X4)|r1_tarski(X3,k3_tarski(X4))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.12/0.36  cnf(c_0_22, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_23, negated_conjecture, (v1_finset_1(esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.36  cnf(c_0_24, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23])])).
% 0.12/0.36  cnf(c_0_26, negated_conjecture, (~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  fof(c_0_27, plain, ![X11]:((r2_hidden(esk1_1(X11),X11)|~v1_finset_1(X11)|v1_finset_1(k3_tarski(X11)))&(~v1_finset_1(esk1_1(X11))|~v1_finset_1(X11)|v1_finset_1(k3_tarski(X11)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).
% 0.12/0.36  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(esk2_0))|~v1_finset_1(k3_tarski(esk2_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.12/0.36  cnf(c_0_29, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))|~v1_finset_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23])])).
% 0.12/0.36  cnf(c_0_30, negated_conjecture, (v1_finset_1(X1)|v1_finset_1(k3_tarski(esk2_0))|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_31, plain, (r2_hidden(esk1_1(X1),X1)|v1_finset_1(k3_tarski(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_32, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_28]), c_0_29])).
% 0.12/0.36  cnf(c_0_33, plain, (v1_finset_1(k3_tarski(X1))|~v1_finset_1(esk1_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.36  cnf(c_0_34, negated_conjecture, (v1_finset_1(esk1_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_23])]), c_0_32])).
% 0.12/0.36  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])]), c_0_32]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 36
% 0.12/0.36  # Proof object clause steps            : 21
% 0.12/0.36  # Proof object formula steps           : 15
% 0.12/0.36  # Proof object conjectures             : 14
% 0.12/0.36  # Proof object clause conjectures      : 11
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 11
% 0.12/0.36  # Proof object initial formulas used   : 7
% 0.12/0.36  # Proof object generating inferences   : 8
% 0.12/0.36  # Proof object simplifying inferences  : 11
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 7
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 12
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 12
% 0.12/0.36  # Processed clauses                    : 22
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 0
% 0.12/0.36  # ...remaining for further processing  : 22
% 0.12/0.36  # Other redundant clauses eliminated   : 0
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 3
% 0.12/0.36  # Generated clauses                    : 14
% 0.12/0.36  # ...of the previous two non-trivial   : 11
% 0.12/0.36  # Contextual simplify-reflections      : 1
% 0.12/0.36  # Paramodulations                      : 14
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 0
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 19
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 1
% 0.12/0.36  #    Non-unit-clauses                  : 15
% 0.12/0.36  # Current number of unprocessed clauses: 1
% 0.12/0.36  # ...number of literals in the above   : 3
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 3
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 16
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 15
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 1
% 0.12/0.36  # Unit Clause-clause subsumption calls : 4
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 1
% 0.12/0.36  # BW rewrite match successes           : 1
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 990
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.026 s
% 0.12/0.36  # System time              : 0.005 s
% 0.12/0.36  # Total time               : 0.031 s
% 0.12/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
