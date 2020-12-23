%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:18 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  87 expanded)
%              Number of clauses        :   27 (  38 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   85 ( 165 expanded)
%              Number of equality atoms :   14 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t27_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t52_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(t41_xboole_1,axiom,(
    ! [X1,X2,X3] : k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t27_relat_1])).

fof(c_0_11,plain,(
    ! [X28,X29,X30] : r1_tarski(k2_xboole_0(k3_xboole_0(X28,X29),k3_xboole_0(X28,X30)),k2_xboole_0(X29,X30)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

fof(c_0_12,plain,(
    ! [X36,X37] : k4_xboole_0(X36,k4_xboole_0(X36,X37)) = k3_xboole_0(X36,X37) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_13,plain,(
    ! [X39,X40,X41] : k4_xboole_0(X39,k4_xboole_0(X40,X41)) = k2_xboole_0(k4_xboole_0(X39,X40),k3_xboole_0(X39,X41)) ),
    inference(variable_rename,[status(thm)],[t52_xboole_1])).

fof(c_0_14,plain,(
    ! [X61,X62] :
      ( ( r1_tarski(k1_relat_1(X61),k1_relat_1(X62))
        | ~ r1_tarski(X61,X62)
        | ~ v1_relat_1(X62)
        | ~ v1_relat_1(X61) )
      & ( r1_tarski(k2_relat_1(X61),k2_relat_1(X62))
        | ~ r1_tarski(X61,X62)
        | ~ v1_relat_1(X62)
        | ~ v1_relat_1(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_15,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_relat_1(esk5_0)
    & ~ r1_tarski(k2_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_16,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X58)
      | v1_relat_1(k4_xboole_0(X58,X59)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

cnf(c_0_17,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X33,X34,X35] : k4_xboole_0(k4_xboole_0(X33,X34),X35) = k4_xboole_0(X33,k2_xboole_0(X34,X35)) ),
    inference(variable_rename,[status(thm)],[t41_xboole_1])).

fof(c_0_21,plain,(
    ! [X26] : k2_xboole_0(X26,k1_xboole_0) = X26 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_22,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18]),c_0_18])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),X3) = k4_xboole_0(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ r1_tarski(X23,X25)
      | r1_tarski(X23,k3_xboole_0(X24,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk5_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),k2_xboole_0(X2,X3)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0) = k4_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,X1)),k2_relat_1(esk5_0))
    | ~ r1_tarski(k4_xboole_0(esk4_0,X1),esk5_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_29]),c_0_34])).

fof(c_0_38,plain,(
    ! [X31,X32] : r1_tarski(k4_xboole_0(X31,X32),X31) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_35,c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(esk4_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_25])).

cnf(c_0_42,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(esk5_0))))
    | ~ r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,X1)),k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),k4_xboole_0(k2_relat_1(esk4_0),k4_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_18]),c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.21/0.36  # No SInE strategy applied
% 0.21/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S4b
% 0.21/0.40  # and selection function SelectCQIPrecW.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.028 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t27_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 0.21/0.40  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.21/0.40  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.21/0.40  fof(t52_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 0.21/0.40  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.21/0.40  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.21/0.40  fof(t41_xboole_1, axiom, ![X1, X2, X3]:k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 0.21/0.40  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.21/0.40  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.21/0.40  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.21/0.40  fof(c_0_10, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t27_relat_1])).
% 0.21/0.40  fof(c_0_11, plain, ![X28, X29, X30]:r1_tarski(k2_xboole_0(k3_xboole_0(X28,X29),k3_xboole_0(X28,X30)),k2_xboole_0(X29,X30)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.21/0.40  fof(c_0_12, plain, ![X36, X37]:k4_xboole_0(X36,k4_xboole_0(X36,X37))=k3_xboole_0(X36,X37), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.21/0.40  fof(c_0_13, plain, ![X39, X40, X41]:k4_xboole_0(X39,k4_xboole_0(X40,X41))=k2_xboole_0(k4_xboole_0(X39,X40),k3_xboole_0(X39,X41)), inference(variable_rename,[status(thm)],[t52_xboole_1])).
% 0.21/0.40  fof(c_0_14, plain, ![X61, X62]:((r1_tarski(k1_relat_1(X61),k1_relat_1(X62))|~r1_tarski(X61,X62)|~v1_relat_1(X62)|~v1_relat_1(X61))&(r1_tarski(k2_relat_1(X61),k2_relat_1(X62))|~r1_tarski(X61,X62)|~v1_relat_1(X62)|~v1_relat_1(X61))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.21/0.40  fof(c_0_15, negated_conjecture, (v1_relat_1(esk4_0)&(v1_relat_1(esk5_0)&~r1_tarski(k2_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.21/0.40  fof(c_0_16, plain, ![X58, X59]:(~v1_relat_1(X58)|v1_relat_1(k4_xboole_0(X58,X59))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.21/0.40  cnf(c_0_17, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.40  cnf(c_0_18, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  fof(c_0_20, plain, ![X33, X34, X35]:k4_xboole_0(k4_xboole_0(X33,X34),X35)=k4_xboole_0(X33,k2_xboole_0(X34,X35)), inference(variable_rename,[status(thm)],[t41_xboole_1])).
% 0.21/0.40  fof(c_0_21, plain, ![X26]:k2_xboole_0(X26,k1_xboole_0)=X26, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.21/0.40  cnf(c_0_22, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_24, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_26, plain, (r1_tarski(k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,k4_xboole_0(X1,X3))),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_17, c_0_18]), c_0_18])).
% 0.21/0.40  cnf(c_0_27, plain, (k4_xboole_0(X1,k4_xboole_0(X2,X3))=k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3)))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.21/0.40  cnf(c_0_28, plain, (k4_xboole_0(k4_xboole_0(X1,X2),X3)=k4_xboole_0(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_29, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.40  fof(c_0_30, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|~r1_tarski(X23,X25)|r1_tarski(X23,k3_xboole_0(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk5_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk5_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (v1_relat_1(k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.40  cnf(c_0_33, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,X2),X3)),k2_xboole_0(X2,X3))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.40  cnf(c_0_34, plain, (k4_xboole_0(k4_xboole_0(X1,X2),k1_xboole_0)=k4_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.40  cnf(c_0_35, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,X1)),k2_relat_1(esk5_0))|~r1_tarski(k4_xboole_0(esk4_0,X1),esk5_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.40  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_29]), c_0_34])).
% 0.21/0.40  fof(c_0_38, plain, ![X31, X32]:r1_tarski(k4_xboole_0(X31,X32),X31), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.21/0.40  cnf(c_0_39, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_35, c_0_18])).
% 0.21/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.40  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_relat_1(X1),k2_relat_1(esk4_0))|~v1_relat_1(X1)|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_25])).
% 0.21/0.40  cnf(c_0_42, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.40  cnf(c_0_43, negated_conjecture, (~r1_tarski(k2_relat_1(k3_xboole_0(esk4_0,esk5_0)),k3_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),k4_xboole_0(X1,k4_xboole_0(X1,k2_relat_1(esk5_0))))|~r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.40  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,X1)),k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_42])])).
% 0.21/0.40  cnf(c_0_46, negated_conjecture, (~r1_tarski(k2_relat_1(k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))),k4_xboole_0(k2_relat_1(esk4_0),k4_xboole_0(k2_relat_1(esk4_0),k2_relat_1(esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_18]), c_0_18])).
% 0.21/0.40  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 48
% 0.21/0.40  # Proof object clause steps            : 27
% 0.21/0.40  # Proof object formula steps           : 21
% 0.21/0.40  # Proof object conjectures             : 15
% 0.21/0.40  # Proof object clause conjectures      : 12
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 12
% 0.21/0.40  # Proof object initial formulas used   : 10
% 0.21/0.40  # Proof object generating inferences   : 10
% 0.21/0.40  # Proof object simplifying inferences  : 11
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 23
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 31
% 0.21/0.40  # Removed in clause preprocessing      : 2
% 0.21/0.40  # Initial clauses in saturation        : 29
% 0.21/0.40  # Processed clauses                    : 244
% 0.21/0.40  # ...of these trivial                  : 38
% 0.21/0.40  # ...subsumed                          : 60
% 0.21/0.40  # ...remaining for further processing  : 146
% 0.21/0.40  # Other redundant clauses eliminated   : 4
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 0
% 0.21/0.40  # Backward-rewritten                   : 14
% 0.21/0.40  # Generated clauses                    : 646
% 0.21/0.40  # ...of the previous two non-trivial   : 429
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 641
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 5
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 103
% 0.21/0.40  #    Positive orientable unit clauses  : 50
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 3
% 0.21/0.40  #    Non-unit-clauses                  : 50
% 0.21/0.40  # Current number of unprocessed clauses: 226
% 0.21/0.40  # ...number of literals in the above   : 405
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 45
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 260
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 231
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 26
% 0.21/0.40  # Unit Clause-clause subsumption calls : 19
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 90
% 0.21/0.40  # BW rewrite match successes           : 9
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 8975
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.042 s
% 0.21/0.40  # System time              : 0.001 s
% 0.21/0.40  # Total time               : 0.043 s
% 0.21/0.40  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
