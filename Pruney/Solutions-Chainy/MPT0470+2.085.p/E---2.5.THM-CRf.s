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
% DateTime   : Thu Dec  3 10:49:06 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 107 expanded)
%              Number of clauses        :   33 (  50 expanded)
%              Number of leaves         :   12 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  124 ( 224 expanded)
%              Number of equality atoms :   28 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t62_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_relat_1(X14)
      | r1_tarski(k1_relat_1(k5_relat_1(X13,X14)),k1_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_15,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
          & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t62_relat_1])).

cnf(c_0_17,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
      | k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X11] :
      ( v1_xboole_0(X11)
      | ~ v1_relat_1(X11)
      | ~ v1_xboole_0(k1_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

fof(c_0_22,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | v1_relat_1(k5_relat_1(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_23,plain,(
    ! [X3,X4] :
      ( ~ r1_tarski(X3,X4)
      | k3_xboole_0(X3,X4) = X3 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ v1_relat_1(X16)
      | r1_tarski(k2_relat_1(k5_relat_1(X15,X16)),k2_relat_1(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_28,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,esk1_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X6)
      | X6 = X7
      | ~ v1_xboole_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_36,plain,
    ( v1_xboole_0(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,esk1_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,esk1_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_25]),c_0_19])])).

fof(c_0_41,plain,(
    ! [X12] :
      ( v1_xboole_0(X12)
      | ~ v1_relat_1(X12)
      | ~ v1_xboole_0(k2_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

cnf(c_0_42,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_18]),c_0_19])])).

cnf(c_0_43,negated_conjecture,
    ( X1 = k5_relat_1(k1_xboole_0,esk1_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relat_1(k5_relat_1(esk1_0,k1_xboole_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( X1 = k5_relat_1(k1_xboole_0,esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_18]),c_0_19])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(k5_relat_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk1_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_45]),c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk1_0) != k1_xboole_0
    | k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_50,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_19])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(k5_relat_1(esk1_0,k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25]),c_0_19])])).

cnf(c_0_53,negated_conjecture,
    ( k5_relat_1(esk1_0,k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_relat_1(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_18]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_B00_00_F1_PI_AE_Q4_CS_SP_PS_S04CN
% 0.13/0.38  # and selection function MSelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.13/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.38  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.13/0.38  fof(t62_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(fc8_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 0.13/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.38  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.13/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.38  fof(t45_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 0.13/0.38  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.13/0.38  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.13/0.38  fof(c_0_12, plain, ![X13, X14]:(~v1_relat_1(X13)|(~v1_relat_1(X14)|r1_tarski(k1_relat_1(k5_relat_1(X13,X14)),k1_relat_1(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.13/0.38  cnf(c_0_13, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X8]:(~v1_xboole_0(X8)|v1_relat_1(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.13/0.38  fof(c_0_16, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>(k5_relat_1(k1_xboole_0,X1)=k1_xboole_0&k5_relat_1(X1,k1_xboole_0)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t62_relat_1])).
% 0.13/0.38  cnf(c_0_17, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.38  cnf(c_0_18, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  fof(c_0_20, negated_conjecture, (v1_relat_1(esk1_0)&(k5_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0|k5_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X11]:(v1_xboole_0(X11)|~v1_relat_1(X11)|~v1_xboole_0(k1_relat_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).
% 0.13/0.38  fof(c_0_22, plain, ![X9, X10]:(~v1_relat_1(X9)|~v1_relat_1(X10)|v1_relat_1(k5_relat_1(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.38  fof(c_0_23, plain, ![X3, X4]:(~r1_tarski(X3,X4)|k3_xboole_0(X3,X4)=X3), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.13/0.38  cnf(c_0_24, plain, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,X1)),k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  fof(c_0_26, plain, ![X5]:k3_xboole_0(X5,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.38  fof(c_0_27, plain, ![X15, X16]:(~v1_relat_1(X15)|(~v1_relat_1(X16)|r1_tarski(k2_relat_1(k5_relat_1(X15,X16)),k2_relat_1(X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).
% 0.13/0.38  cnf(c_0_28, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_29, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.38  cnf(c_0_30, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,esk1_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_32, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.38  cnf(c_0_33, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  fof(c_0_35, plain, ![X6, X7]:(~v1_xboole_0(X6)|X6=X7|~v1_xboole_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.13/0.38  cnf(c_0_36, plain, (v1_xboole_0(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(k5_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (k1_relat_1(k5_relat_1(k1_xboole_0,esk1_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.38  cnf(c_0_38, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)|~v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  cnf(c_0_39, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v1_xboole_0(k5_relat_1(k1_xboole_0,esk1_0))|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_25]), c_0_19])])).
% 0.13/0.38  fof(c_0_41, plain, ![X12]:(v1_xboole_0(X12)|~v1_relat_1(X12)|~v1_xboole_0(k2_relat_1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.13/0.38  cnf(c_0_42, plain, (r1_tarski(k2_relat_1(k5_relat_1(X1,k1_xboole_0)),k1_xboole_0)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_18]), c_0_19])])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (X1=k5_relat_1(k1_xboole_0,esk1_0)|~v1_relat_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_44, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relat_1(k5_relat_1(esk1_0,k1_xboole_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_25])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (X1=k5_relat_1(k1_xboole_0,esk1_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_18]), c_0_19])])).
% 0.13/0.38  cnf(c_0_47, plain, (v1_xboole_0(k5_relat_1(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(k5_relat_1(X1,X2)))), inference(spm,[status(thm)],[c_0_44, c_0_29])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k2_relat_1(k5_relat_1(esk1_0,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_45]), c_0_32])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k5_relat_1(k1_xboole_0,esk1_0)!=k1_xboole_0|k5_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (k5_relat_1(k1_xboole_0,esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_19])).
% 0.13/0.38  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (v1_xboole_0(k5_relat_1(esk1_0,k1_xboole_0))|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_25]), c_0_19])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (k5_relat_1(esk1_0,k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_50])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (~v1_relat_1(k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_18]), c_0_19])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 56
% 0.13/0.38  # Proof object clause steps            : 33
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 12
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 19
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 12
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 14
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 14
% 0.13/0.38  # Processed clauses                    : 56
% 0.13/0.38  # ...of these trivial                  : 1
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 53
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 4
% 0.13/0.38  # Backward-rewritten                   : 6
% 0.13/0.38  # Generated clauses                    : 58
% 0.13/0.38  # ...of the previous two non-trivial   : 43
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 58
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 0
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 29
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 15
% 0.13/0.38  # ...number of literals in the above   : 41
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 24
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 44
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 38
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 6
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 5
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1712
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.027 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
