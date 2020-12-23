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
% DateTime   : Thu Dec  3 10:50:37 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   37 (  71 expanded)
%              Number of clauses        :   19 (  32 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 116 expanded)
%              Number of equality atoms :   28 (  55 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t149_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t145_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,X1) = k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t150_relat_1,conjecture,(
    ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_9,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r1_xboole_0(X5,X6)
        | r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)) )
      & ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12] : k4_xboole_0(X11,k4_xboole_0(X11,X12)) = k3_xboole_0(X11,X12) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X14] : r1_xboole_0(X14,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_14,plain,(
    ! [X37] :
      ( ~ v1_relat_1(X37)
      | k9_relat_1(X37,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).

fof(c_0_15,plain,(
    ! [X27,X28,X31,X33,X34] :
      ( ( ~ v1_relat_1(X27)
        | ~ r2_hidden(X28,X27)
        | X28 = k4_tarski(esk2_2(X27,X28),esk3_2(X27,X28)) )
      & ( r2_hidden(esk4_1(X31),X31)
        | v1_relat_1(X31) )
      & ( esk4_1(X31) != k4_tarski(X33,X34)
        | v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_16,plain,(
    ! [X35,X36] :
      ( ~ v1_relat_1(X36)
      | k9_relat_1(X36,X35) = k9_relat_1(X36,k3_xboole_0(k1_relat_1(X36),X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).

cnf(c_0_17,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_21,plain,(
    ! [X13] : k4_xboole_0(k1_xboole_0,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_22,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] : k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t150_relat_1])).

cnf(c_0_26,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k9_relat_1(X1,X2) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_22,c_0_12])).

cnf(c_0_28,plain,
    ( k9_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_29,negated_conjecture,(
    k9_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_26]),c_0_26])).

cnf(c_0_31,plain,
    ( k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2))) = k9_relat_1(X1,X2)
    | r2_hidden(esk4_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_32,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_33,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_26]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(k1_xboole_0,esk5_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_32]),c_0_26]),c_0_26]),c_0_33])).

cnf(c_0_36,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:04:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B00_00_F1_SE_CS_SP_PS_S071I
% 0.13/0.37  # and selection function SelectCQArEqLast.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.37  fof(t149_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 0.13/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.13/0.37  fof(t145_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k9_relat_1(X2,X1)=k9_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 0.13/0.37  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.37  fof(t150_relat_1, conjecture, ![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 0.13/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.37  fof(c_0_9, plain, ![X5, X6, X8, X9, X10]:((r1_xboole_0(X5,X6)|r2_hidden(esk1_2(X5,X6),k3_xboole_0(X5,X6)))&(~r2_hidden(X10,k3_xboole_0(X8,X9))|~r1_xboole_0(X8,X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.37  fof(c_0_10, plain, ![X11, X12]:k4_xboole_0(X11,k4_xboole_0(X11,X12))=k3_xboole_0(X11,X12), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.37  cnf(c_0_11, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_13, plain, ![X14]:r1_xboole_0(X14,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.37  fof(c_0_14, plain, ![X37]:(~v1_relat_1(X37)|k9_relat_1(X37,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t149_relat_1])])).
% 0.13/0.37  fof(c_0_15, plain, ![X27, X28, X31, X33, X34]:((~v1_relat_1(X27)|(~r2_hidden(X28,X27)|X28=k4_tarski(esk2_2(X27,X28),esk3_2(X27,X28))))&((r2_hidden(esk4_1(X31),X31)|v1_relat_1(X31))&(esk4_1(X31)!=k4_tarski(X33,X34)|v1_relat_1(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.13/0.37  fof(c_0_16, plain, ![X35, X36]:(~v1_relat_1(X36)|k9_relat_1(X36,X35)=k9_relat_1(X36,k3_xboole_0(k1_relat_1(X36),X35))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_relat_1])])).
% 0.13/0.37  cnf(c_0_17, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.37  cnf(c_0_18, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_19, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  cnf(c_0_20, plain, (r2_hidden(esk4_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_21, plain, ![X13]:k4_xboole_0(k1_xboole_0,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.37  cnf(c_0_22, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_23, plain, (~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_24, plain, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|r2_hidden(esk4_1(X1),X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  fof(c_0_25, negated_conjecture, ~(![X1]:k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(assume_negation,[status(cth)],[t150_relat_1])).
% 0.13/0.37  cnf(c_0_26, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_27, plain, (k9_relat_1(X1,X2)=k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_22, c_0_12])).
% 0.13/0.37  cnf(c_0_28, plain, (k9_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)),k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  fof(c_0_29, negated_conjecture, k9_relat_1(k1_xboole_0,esk5_0)!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.37  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_26]), c_0_26])).
% 0.13/0.37  cnf(c_0_31, plain, (k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X2)))=k9_relat_1(X1,X2)|r2_hidden(esk4_1(X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_20])).
% 0.13/0.37  cnf(c_0_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.37  cnf(c_0_33, plain, (k9_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_26]), c_0_26])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (k9_relat_1(k1_xboole_0,esk5_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_35, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_32]), c_0_26]), c_0_26]), c_0_33])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 37
% 0.13/0.37  # Proof object clause steps            : 19
% 0.13/0.37  # Proof object formula steps           : 18
% 0.13/0.37  # Proof object conjectures             : 5
% 0.13/0.37  # Proof object clause conjectures      : 2
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 9
% 0.13/0.37  # Proof object initial formulas used   : 9
% 0.13/0.37  # Proof object generating inferences   : 7
% 0.13/0.37  # Proof object simplifying inferences  : 11
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 14
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 23
% 0.13/0.37  # Removed in clause preprocessing      : 2
% 0.13/0.37  # Initial clauses in saturation        : 21
% 0.13/0.37  # Processed clauses                    : 63
% 0.13/0.37  # ...of these trivial                  : 2
% 0.13/0.37  # ...subsumed                          : 3
% 0.13/0.37  # ...remaining for further processing  : 58
% 0.13/0.37  # Other redundant clauses eliminated   : 5
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 32
% 0.13/0.37  # ...of the previous two non-trivial   : 28
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 24
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 8
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 30
% 0.13/0.37  #    Positive orientable unit clauses  : 9
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 3
% 0.13/0.37  #    Non-unit-clauses                  : 18
% 0.13/0.37  # Current number of unprocessed clauses: 6
% 0.13/0.37  # ...number of literals in the above   : 14
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 25
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 29
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 26
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 3
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 9
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1831
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.027 s
% 0.13/0.37  # System time              : 0.006 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
