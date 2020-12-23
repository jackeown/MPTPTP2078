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
% DateTime   : Thu Dec  3 10:54:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   39 (  56 expanded)
%              Number of clauses        :   18 (  23 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   97 ( 120 expanded)
%              Number of equality atoms :   32 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(t52_funct_1,axiom,(
    ! [X1] : v2_funct_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(t67_funct_1,conjecture,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(c_0_10,plain,(
    ! [X14] :
      ( ( k2_relat_1(X14) = k1_relat_1(k2_funct_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( k1_relat_1(X14) = k2_relat_1(k2_funct_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_11,plain,(
    ! [X13] : v2_funct_1(k6_relat_1(X13)) ),
    inference(variable_rename,[status(thm)],[t52_funct_1])).

fof(c_0_12,plain,(
    ! [X8] :
      ( k1_relat_1(k6_relat_1(X8)) = X8
      & k2_relat_1(k6_relat_1(X8)) = X8 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_13,plain,(
    ! [X12] :
      ( v1_relat_1(k6_relat_1(X12))
      & v1_funct_1(k6_relat_1(X12)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_14,plain,(
    ! [X7] : v1_relat_1(k6_relat_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_15,plain,(
    ! [X11] :
      ( ( v1_relat_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( v1_funct_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ r1_tarski(k1_relat_1(X10),X9)
      | k5_relat_1(k6_relat_1(X9),X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_17,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_24,plain,(
    ! [X15] :
      ( ( k5_relat_1(X15,k2_funct_1(X15)) = k6_relat_1(k1_relat_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( k5_relat_1(k2_funct_1(X15),X15) = k6_relat_1(k2_relat_1(X15))
        | ~ v2_funct_1(X15)
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(assume_negation,[status(cth)],[t67_funct_1])).

cnf(c_0_26,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k1_relat_1(k2_funct_1(k6_relat_1(X1))) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_funct_1(k6_relat_1(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_32,negated_conjecture,(
    k2_funct_1(k6_relat_1(esk1_0)) != k6_relat_1(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_33,plain,
    ( k5_relat_1(k6_relat_1(X1),k2_funct_1(k6_relat_1(X2))) = k2_funct_1(k6_relat_1(X2))
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( k5_relat_1(k6_relat_1(X1),k2_funct_1(k6_relat_1(X1))) = k6_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_18]),c_0_31]),c_0_20]),c_0_21])])).

cnf(c_0_36,negated_conjecture,
    ( k2_funct_1(k6_relat_1(esk1_0)) != k6_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_PS_S0i
% 0.13/0.38  # and selection function SelectDiffNegLit.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.38  fof(t52_funct_1, axiom, ![X1]:v2_funct_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 0.13/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 0.13/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.13/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.38  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.38  fof(t77_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k5_relat_1(k6_relat_1(X1),X2)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 0.13/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.38  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 0.13/0.38  fof(t67_funct_1, conjecture, ![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 0.13/0.38  fof(c_0_10, plain, ![X14]:((k2_relat_1(X14)=k1_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(k1_relat_1(X14)=k2_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X13]:v2_funct_1(k6_relat_1(X13)), inference(variable_rename,[status(thm)],[t52_funct_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X8]:(k1_relat_1(k6_relat_1(X8))=X8&k2_relat_1(k6_relat_1(X8))=X8), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.13/0.38  fof(c_0_13, plain, ![X12]:(v1_relat_1(k6_relat_1(X12))&v1_funct_1(k6_relat_1(X12))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.13/0.38  fof(c_0_14, plain, ![X7]:v1_relat_1(k6_relat_1(X7)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.38  fof(c_0_15, plain, ![X11]:((v1_relat_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(v1_funct_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X9, X10]:(~v1_relat_1(X10)|(~r1_tarski(k1_relat_1(X10),X9)|k5_relat_1(k6_relat_1(X9),X10)=X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).
% 0.13/0.38  cnf(c_0_17, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_19, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_20, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_21, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  fof(c_0_23, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.38  fof(c_0_24, plain, ![X15]:((k5_relat_1(X15,k2_funct_1(X15))=k6_relat_1(k1_relat_1(X15))|~v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))&(k5_relat_1(k2_funct_1(X15),X15)=k6_relat_1(k2_relat_1(X15))|~v2_funct_1(X15)|(~v1_relat_1(X15)|~v1_funct_1(X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 0.13/0.38  fof(c_0_25, negated_conjecture, ~(![X1]:k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(assume_negation,[status(cth)],[t67_funct_1])).
% 0.13/0.38  cnf(c_0_26, plain, (k5_relat_1(k6_relat_1(X2),X1)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_27, plain, (k1_relat_1(k2_funct_1(k6_relat_1(X1)))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_28, plain, (v1_relat_1(k2_funct_1(k6_relat_1(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.38  cnf(c_0_30, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_31, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_32, negated_conjecture, k2_funct_1(k6_relat_1(esk1_0))!=k6_relat_1(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.13/0.38  cnf(c_0_33, plain, (k5_relat_1(k6_relat_1(X1),k2_funct_1(k6_relat_1(X2)))=k2_funct_1(k6_relat_1(X2))|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.13/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_35, plain, (k5_relat_1(k6_relat_1(X1),k2_funct_1(k6_relat_1(X1)))=k6_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_18]), c_0_31]), c_0_20]), c_0_21])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k2_funct_1(k6_relat_1(esk1_0))!=k6_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_37, plain, (k2_funct_1(k6_relat_1(X1))=k6_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 39
% 0.13/0.38  # Proof object clause steps            : 18
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 5
% 0.13/0.38  # Proof object clause conjectures      : 2
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 11
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 5
% 0.13/0.38  # Proof object simplifying inferences  : 16
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 18
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 18
% 0.13/0.38  # Processed clauses                    : 54
% 0.13/0.38  # ...of these trivial                  : 3
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 51
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 14
% 0.13/0.38  # Generated clauses                    : 28
% 0.13/0.38  # ...of the previous two non-trivial   : 28
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 25
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 19
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 0
% 0.13/0.38  #    Non-unit-clauses                  : 11
% 0.13/0.38  # Current number of unprocessed clauses: 7
% 0.13/0.38  # ...number of literals in the above   : 7
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 30
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 56
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 43
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 3
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 16
% 0.13/0.38  # BW rewrite match successes           : 3
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1637
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.002 s
% 0.13/0.38  # Total time               : 0.032 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
