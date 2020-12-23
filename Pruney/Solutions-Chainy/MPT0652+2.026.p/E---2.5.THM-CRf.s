%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 210 expanded)
%              Number of clauses        :   26 (  72 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  124 ( 775 expanded)
%              Number of equality atoms :   40 ( 277 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
          & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1)
            & k2_relat_1(k5_relat_1(k2_funct_1(X1),X1)) = k2_relat_1(X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_funct_1])).

fof(c_0_10,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v2_funct_1(X13)
      | k2_funct_1(X13) = k4_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

fof(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v2_funct_1(esk1_0)
    & ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
      | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
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

cnf(c_0_13,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X6)
      | r1_tarski(k10_relat_1(X6,X5),k1_relat_1(X6)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_18,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k10_relat_1(X7,k2_relat_1(X7)) = k1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_19,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( k2_funct_1(esk1_0) = k4_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_21,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X10] :
      ( ( k2_relat_1(X10) = k1_relat_1(k4_relat_1(X10))
        | ~ v1_relat_1(X10) )
      & ( k1_relat_1(X10) = k2_relat_1(k4_relat_1(X10))
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_25,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | v1_relat_1(k4_relat_1(X3)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_26,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ v1_relat_1(X9)
      | k1_relat_1(k5_relat_1(X8,X9)) = k10_relat_1(X8,k1_relat_1(X9)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_27,negated_conjecture,
    ( k2_relat_1(k4_relat_1(esk1_0)) = k1_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk1_0)) = k2_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_20]),c_0_14]),c_0_15]),c_0_16])])).

fof(c_0_29,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ r1_tarski(k1_relat_1(X11),k2_relat_1(X12))
      | k2_relat_1(k5_relat_1(X12,X11)) = k2_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
    | k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k10_relat_1(k4_relat_1(esk1_0),k1_relat_1(esk1_0)) = k2_relat_1(esk1_0)
    | ~ v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_28])).

cnf(c_0_36,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
    | k2_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_20]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0)) = k2_relat_1(esk1_0)
    | ~ v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_16])])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k4_relat_1(esk1_0),X1)) = k2_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(esk1_0))
    | ~ v1_relat_1(k4_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk1_0))
    | ~ v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( k2_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0)) != k2_relat_1(esk1_0)
    | ~ v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_relat_1(k4_relat_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_16])]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_32]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:51:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t59_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 0.14/0.38  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 0.14/0.38  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.14/0.38  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.14/0.38  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 0.14/0.38  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 0.14/0.38  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.14/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.14/0.38  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 0.14/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1)&k2_relat_1(k5_relat_1(k2_funct_1(X1),X1))=k2_relat_1(X1))))), inference(assume_negation,[status(cth)],[t59_funct_1])).
% 0.14/0.38  fof(c_0_10, plain, ![X13]:(~v1_relat_1(X13)|~v1_funct_1(X13)|(~v2_funct_1(X13)|k2_funct_1(X13)=k4_relat_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.14/0.38  fof(c_0_11, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(v2_funct_1(esk1_0)&(k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.38  fof(c_0_12, plain, ![X14]:((k2_relat_1(X14)=k1_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(k1_relat_1(X14)=k2_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.14/0.38  cnf(c_0_13, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (v2_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_17, plain, ![X5, X6]:(~v1_relat_1(X6)|r1_tarski(k10_relat_1(X6,X5),k1_relat_1(X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.14/0.38  fof(c_0_18, plain, ![X7]:(~v1_relat_1(X7)|k10_relat_1(X7,k2_relat_1(X7))=k1_relat_1(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 0.14/0.38  cnf(c_0_19, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_20, negated_conjecture, (k2_funct_1(esk1_0)=k4_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])])).
% 0.14/0.38  cnf(c_0_21, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_22, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_23, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.38  fof(c_0_24, plain, ![X10]:((k2_relat_1(X10)=k1_relat_1(k4_relat_1(X10))|~v1_relat_1(X10))&(k1_relat_1(X10)=k2_relat_1(k4_relat_1(X10))|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.14/0.38  fof(c_0_25, plain, ![X3]:(~v1_relat_1(X3)|v1_relat_1(k4_relat_1(X3))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.14/0.38  fof(c_0_26, plain, ![X8, X9]:(~v1_relat_1(X8)|(~v1_relat_1(X9)|k1_relat_1(k5_relat_1(X8,X9))=k10_relat_1(X8,k1_relat_1(X9)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (k2_relat_1(k4_relat_1(esk1_0))=k1_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_14]), c_0_15]), c_0_16])])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (k1_relat_1(k4_relat_1(esk1_0))=k2_relat_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_20]), c_0_14]), c_0_15]), c_0_16])])).
% 0.14/0.38  fof(c_0_29, plain, ![X11, X12]:(~v1_relat_1(X11)|(~v1_relat_1(X12)|(~r1_tarski(k1_relat_1(X11),k2_relat_1(X12))|k2_relat_1(k5_relat_1(X12,X11))=k2_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 0.14/0.38  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_31, plain, (k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_32, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_33, negated_conjecture, (k1_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k2_funct_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_34, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k10_relat_1(k4_relat_1(esk1_0),k1_relat_1(esk1_0))=k2_relat_1(esk1_0)|~v1_relat_1(k4_relat_1(esk1_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_27]), c_0_28])).
% 0.14/0.38  cnf(c_0_36, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_37, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (k1_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|k2_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_20]), c_0_20])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (k1_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0))=k2_relat_1(esk1_0)|~v1_relat_1(k4_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_16])])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k2_relat_1(k5_relat_1(k4_relat_1(esk1_0),X1))=k2_relat_1(X1)|~r1_tarski(k1_relat_1(X1),k1_relat_1(esk1_0))|~v1_relat_1(k4_relat_1(esk1_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_relat_1(esk1_0))|~v1_relat_1(k4_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k2_relat_1(k5_relat_1(k4_relat_1(esk1_0),esk1_0))!=k2_relat_1(esk1_0)|~v1_relat_1(k4_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (~v1_relat_1(k4_relat_1(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_16])]), c_0_42])).
% 0.14/0.38  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_32]), c_0_16])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 45
% 0.14/0.38  # Proof object clause steps            : 26
% 0.14/0.38  # Proof object formula steps           : 19
% 0.14/0.38  # Proof object conjectures             : 18
% 0.14/0.38  # Proof object clause conjectures      : 15
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 13
% 0.14/0.38  # Proof object initial formulas used   : 9
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 22
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 15
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 15
% 0.14/0.38  # Processed clauses                    : 60
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 15
% 0.14/0.38  # ...remaining for further processing  : 45
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 60
% 0.14/0.38  # ...of the previous two non-trivial   : 59
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 60
% 0.14/0.38  # Factorizations                       : 0
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
% 0.14/0.38  # Current number of processed clauses  : 29
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 22
% 0.14/0.38  # Current number of unprocessed clauses: 29
% 0.14/0.38  # ...number of literals in the above   : 138
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 16
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 126
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 105
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 17
% 0.14/0.38  # Unit Clause-clause subsumption calls : 7
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2219
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.028 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.033 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
