%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 189 expanded)
%              Number of clauses        :   24 (  84 expanded)
%              Number of leaves         :    7 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 590 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(t100_zfmisc_1,axiom,(
    ! [X1] : r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(fc17_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => v1_finset_1(k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_finset_1)).

fof(t25_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
    <=> v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_finset_1)).

fof(l22_finset_1,axiom,(
    ! [X1] :
      ( ( v1_finset_1(X1)
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => v1_finset_1(X2) ) )
     => v1_finset_1(k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_finset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t56_setfam_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(k3_tarski(X1),X2)
        & r2_hidden(X3,X1) )
     => r1_tarski(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(c_0_7,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | ~ v1_finset_1(X14)
      | v1_finset_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

fof(c_0_8,plain,(
    ! [X6] : r1_tarski(X6,k1_zfmisc_1(k3_tarski(X6))) ),
    inference(variable_rename,[status(thm)],[t100_zfmisc_1])).

cnf(c_0_9,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X10] :
      ( ~ v1_finset_1(X10)
      | v1_finset_1(k1_zfmisc_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_finset_1(X1)
          & ! [X2] :
              ( r2_hidden(X2,X1)
             => v1_finset_1(X2) ) )
      <=> v1_finset_1(k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t25_finset_1])).

cnf(c_0_13,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_zfmisc_1(k3_tarski(X1))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( v1_finset_1(k1_zfmisc_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ! [X17] :
      ( ( r2_hidden(esk3_0,esk2_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ v1_finset_1(esk3_0)
        | ~ v1_finset_1(esk2_0)
        | ~ v1_finset_1(k3_tarski(esk2_0)) )
      & ( v1_finset_1(esk2_0)
        | v1_finset_1(k3_tarski(esk2_0)) )
      & ( ~ r2_hidden(X17,esk2_0)
        | v1_finset_1(X17)
        | v1_finset_1(k3_tarski(esk2_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).

fof(c_0_16,plain,(
    ! [X11] :
      ( ( r2_hidden(esk1_1(X11),X11)
        | ~ v1_finset_1(X11)
        | v1_finset_1(k3_tarski(X11)) )
      & ( ~ v1_finset_1(esk1_1(X11))
        | ~ v1_finset_1(X11)
        | v1_finset_1(k3_tarski(X11)) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).

cnf(c_0_17,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k3_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_finset_1(esk2_0)
    | v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,negated_conjecture,
    ( v1_finset_1(X1)
    | v1_finset_1(k3_tarski(esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_finset_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_23,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k3_tarski(X7),X8)
      | ~ r2_hidden(X9,X7)
      | r1_tarski(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v1_finset_1(k3_tarski(X1))
    | ~ v1_finset_1(esk1_1(X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( v1_finset_1(esk1_1(esk2_0))
    | v1_finset_1(k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_28,plain,
    ( r1_tarski(X3,X2)
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_22])])).

cnf(c_0_31,negated_conjecture,
    ( v1_finset_1(k3_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_finset_1(esk3_0)
    | ~ v1_finset_1(esk2_0)
    | ~ v1_finset_1(k3_tarski(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_finset_1(k3_tarski(esk2_0))
    | ~ v1_finset_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_22])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_finset_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_31])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_36]),c_0_31])]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_____0026_C18_F1_SE_CS_SP_S4S
% 0.20/0.37  # and selection function SelectNewComplexAHPNS.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.027 s
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t13_finset_1, axiom, ![X1, X2]:((r1_tarski(X1,X2)&v1_finset_1(X2))=>v1_finset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 0.20/0.37  fof(t100_zfmisc_1, axiom, ![X1]:r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 0.20/0.37  fof(fc17_finset_1, axiom, ![X1]:(v1_finset_1(X1)=>v1_finset_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc17_finset_1)).
% 0.20/0.37  fof(t25_finset_1, conjecture, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_finset_1)).
% 0.20/0.37  fof(l22_finset_1, axiom, ![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))=>v1_finset_1(k3_tarski(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_finset_1)).
% 0.20/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.37  fof(t56_setfam_1, axiom, ![X1, X2, X3]:((r1_tarski(k3_tarski(X1),X2)&r2_hidden(X3,X1))=>r1_tarski(X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 0.20/0.37  fof(c_0_7, plain, ![X13, X14]:(~r1_tarski(X13,X14)|~v1_finset_1(X14)|v1_finset_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).
% 0.20/0.37  fof(c_0_8, plain, ![X6]:r1_tarski(X6,k1_zfmisc_1(k3_tarski(X6))), inference(variable_rename,[status(thm)],[t100_zfmisc_1])).
% 0.20/0.37  cnf(c_0_9, plain, (v1_finset_1(X1)|~r1_tarski(X1,X2)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.37  cnf(c_0_10, plain, (r1_tarski(X1,k1_zfmisc_1(k3_tarski(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  fof(c_0_11, plain, ![X10]:(~v1_finset_1(X10)|v1_finset_1(k1_zfmisc_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc17_finset_1])])).
% 0.20/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:((v1_finset_1(X1)&![X2]:(r2_hidden(X2,X1)=>v1_finset_1(X2)))<=>v1_finset_1(k3_tarski(X1)))), inference(assume_negation,[status(cth)],[t25_finset_1])).
% 0.20/0.37  cnf(c_0_13, plain, (v1_finset_1(X1)|~v1_finset_1(k1_zfmisc_1(k3_tarski(X1)))), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.20/0.37  cnf(c_0_14, plain, (v1_finset_1(k1_zfmisc_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  fof(c_0_15, negated_conjecture, ![X17]:(((r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0)))&(~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))))&((v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0)))&(~r2_hidden(X17,esk2_0)|v1_finset_1(X17)|v1_finset_1(k3_tarski(esk2_0))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])])])).
% 0.20/0.37  fof(c_0_16, plain, ![X11]:((r2_hidden(esk1_1(X11),X11)|~v1_finset_1(X11)|v1_finset_1(k3_tarski(X11)))&(~v1_finset_1(esk1_1(X11))|~v1_finset_1(X11)|v1_finset_1(k3_tarski(X11)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l22_finset_1])])])])).
% 0.20/0.37  cnf(c_0_17, plain, (v1_finset_1(X1)|~v1_finset_1(k3_tarski(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (v1_finset_1(esk2_0)|v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  fof(c_0_19, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.37  cnf(c_0_20, negated_conjecture, (v1_finset_1(X1)|v1_finset_1(k3_tarski(esk2_0))|~r2_hidden(X1,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_21, plain, (r2_hidden(esk1_1(X1),X1)|v1_finset_1(k3_tarski(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (v1_finset_1(esk2_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  fof(c_0_23, plain, ![X7, X8, X9]:(~r1_tarski(k3_tarski(X7),X8)|~r2_hidden(X9,X7)|r1_tarski(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_setfam_1])])).
% 0.20/0.37  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_26, plain, (v1_finset_1(k3_tarski(X1))|~v1_finset_1(esk1_1(X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (v1_finset_1(esk1_1(esk2_0))|v1_finset_1(k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.20/0.37  cnf(c_0_28, plain, (r1_tarski(X3,X2)|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_29, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk3_0,esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_22])])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (v1_finset_1(k3_tarski(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_22])])).
% 0.20/0.37  cnf(c_0_32, negated_conjecture, (~v1_finset_1(esk3_0)|~v1_finset_1(esk2_0)|~v1_finset_1(k3_tarski(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_33, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (r2_hidden(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (~v1_finset_1(k3_tarski(esk2_0))|~v1_finset_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_22])])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (r1_tarski(esk3_0,k3_tarski(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (~v1_finset_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_31])])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_36]), c_0_31])]), c_0_37]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 39
% 0.20/0.37  # Proof object clause steps            : 24
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 16
% 0.20/0.37  # Proof object clause conjectures      : 13
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 8
% 0.20/0.37  # Proof object simplifying inferences  : 16
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 13
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 13
% 0.20/0.37  # Processed clauses                    : 24
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 24
% 0.20/0.37  # Other redundant clauses eliminated   : 2
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 6
% 0.20/0.37  # Generated clauses                    : 16
% 0.20/0.37  # ...of the previous two non-trivial   : 14
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 14
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 2
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
% 0.20/0.37  # Current number of processed clauses  : 16
% 0.20/0.37  #    Positive orientable unit clauses  : 6
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 1
% 0.20/0.37  #    Non-unit-clauses                  : 9
% 0.20/0.37  # Current number of unprocessed clauses: 3
% 0.20/0.37  # ...number of literals in the above   : 7
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 6
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 16
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 15
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 0
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 3
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 1008
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.025 s
% 0.20/0.37  # System time              : 0.006 s
% 0.20/0.37  # Total time               : 0.031 s
% 0.20/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
