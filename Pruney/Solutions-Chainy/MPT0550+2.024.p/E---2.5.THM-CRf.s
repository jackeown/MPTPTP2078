%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   39 (  62 expanded)
%              Number of clauses        :   22 (  26 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 146 expanded)
%              Number of equality atoms :   21 (  54 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( X1 != k1_xboole_0
          & r1_tarski(X1,k1_relat_1(X2))
          & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(fc9_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(fc10_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( X1 != k1_xboole_0
            & r1_tarski(X1,k1_relat_1(X2))
            & k9_relat_1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t152_relat_1])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(X11,k1_relat_1(X12))
      | k1_relat_1(k7_relat_1(X12,X11)) = X11 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & esk2_0 != k1_xboole_0
    & r1_tarski(esk2_0,k1_relat_1(esk3_0))
    & k9_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | v1_relat_1(k7_relat_1(X5,X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | k2_relat_1(k7_relat_1(X10,X9)) = k9_relat_1(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_13,plain,(
    ! [X3] :
      ( ~ v1_xboole_0(X3)
      | X3 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_14,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

cnf(c_0_15,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X8] :
      ( v1_xboole_0(X8)
      | ~ v1_relat_1(X8)
      | ~ v1_xboole_0(k2_relat_1(X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).

cnf(c_0_18,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X7] :
      ( ~ v1_xboole_0(X7)
      | v1_xboole_0(k1_relat_1(X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).

cnf(c_0_23,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk2_0,k1_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_16])).

cnf(c_0_28,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk3_0,esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk3_0,X1))
    | ~ v1_xboole_0(k9_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k9_relat_1(esk3_0,esk2_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(k7_relat_1(esk3_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(k7_relat_1(esk3_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_37,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:53:16 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.36  # and selection function PSelectSmallestOrientable.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.026 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t152_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 0.13/0.36  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 0.13/0.36  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.36  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.36  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.36  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.13/0.36  fof(fc9_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 0.13/0.36  fof(fc10_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_xboole_0(k1_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 0.13/0.36  fof(c_0_8, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>~(((X1!=k1_xboole_0&r1_tarski(X1,k1_relat_1(X2)))&k9_relat_1(X2,X1)=k1_xboole_0)))), inference(assume_negation,[status(cth)],[t152_relat_1])).
% 0.13/0.36  fof(c_0_9, plain, ![X11, X12]:(~v1_relat_1(X12)|(~r1_tarski(X11,k1_relat_1(X12))|k1_relat_1(k7_relat_1(X12,X11))=X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.13/0.36  fof(c_0_10, negated_conjecture, (v1_relat_1(esk3_0)&((esk2_0!=k1_xboole_0&r1_tarski(esk2_0,k1_relat_1(esk3_0)))&k9_relat_1(esk3_0,esk2_0)=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X5, X6]:(~v1_relat_1(X5)|v1_relat_1(k7_relat_1(X5,X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.37  fof(c_0_12, plain, ![X9, X10]:(~v1_relat_1(X10)|k2_relat_1(k7_relat_1(X10,X9))=k9_relat_1(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.37  fof(c_0_13, plain, ![X3]:(~v1_xboole_0(X3)|X3=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.37  fof(c_0_14, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.13/0.37  cnf(c_0_15, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_17, plain, ![X8]:(v1_xboole_0(X8)|~v1_relat_1(X8)|~v1_xboole_0(k2_relat_1(X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_relat_1])])])).
% 0.13/0.37  cnf(c_0_18, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_19, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_20, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_21, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_22, plain, ![X7]:(~v1_xboole_0(X7)|v1_xboole_0(k1_relat_1(X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_relat_1])])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r1_tarski(esk2_0,k1_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_25, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_19, c_0_16])).
% 0.13/0.37  cnf(c_0_28, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.37  cnf(c_0_29, plain, (v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (k1_relat_1(k7_relat_1(esk3_0,esk2_0))=esk2_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (v1_xboole_0(k7_relat_1(esk3_0,X1))|~v1_xboole_0(k9_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (k9_relat_1(esk3_0,esk2_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_33, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_21, c_0_28])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(k7_relat_1(esk3_0,esk2_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (v1_xboole_0(k7_relat_1(esk3_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.13/0.37  cnf(c_0_37, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_36]), c_0_37]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 39
% 0.13/0.37  # Proof object clause steps            : 22
% 0.13/0.37  # Proof object formula steps           : 17
% 0.13/0.37  # Proof object conjectures             : 16
% 0.13/0.37  # Proof object clause conjectures      : 13
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 11
% 0.13/0.37  # Proof object initial formulas used   : 8
% 0.13/0.37  # Proof object generating inferences   : 9
% 0.13/0.37  # Proof object simplifying inferences  : 7
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 8
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 11
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 11
% 0.13/0.37  # Processed clauses                    : 38
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 38
% 0.13/0.37  # Other redundant clauses eliminated   : 0
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 30
% 0.13/0.37  # ...of the previous two non-trivial   : 29
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 30
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 0
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
% 0.13/0.37  # Current number of processed clauses  : 24
% 0.13/0.37  #    Positive orientable unit clauses  : 13
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 10
% 0.13/0.37  # Current number of unprocessed clauses: 11
% 0.13/0.37  # ...number of literals in the above   : 16
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 14
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 11
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 11
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.37  # Unit Clause-clause subsumption calls : 0
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 4
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1023
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.026 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.031 s
% 0.13/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
