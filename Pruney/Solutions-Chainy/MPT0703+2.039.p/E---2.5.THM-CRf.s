%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:19 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  92 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 285 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t158_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
          & r1_tarski(X1,k2_relat_1(X3)) )
       => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t94_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k5_relat_1(k6_relat_1(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

fof(c_0_11,plain,(
    ! [X7,X8] :
      ( ~ v1_relat_1(X7)
      | ~ v1_relat_1(X8)
      | v1_relat_1(k5_relat_1(X7,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k2_relat_1(esk3_0))
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(X10,X11)
      | k7_relat_1(k7_relat_1(X12,X11),X10) = k7_relat_1(X12,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

fof(c_0_14,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v1_funct_1(X22)
      | ~ r1_tarski(X21,k2_relat_1(X22))
      | k9_relat_1(X22,k10_relat_1(X22,X21)) = X21 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_15,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X9] : v1_relat_1(k6_relat_1(X9)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_18,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,X15) = k5_relat_1(k6_relat_1(X15),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ v1_funct_1(X20)
      | r1_tarski(k9_relat_1(X20,k10_relat_1(X20,X19)),X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_20,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X14)
      | k2_relat_1(k7_relat_1(X14,X13)) = k9_relat_1(X14,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_22,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( v1_relat_1(k5_relat_1(X1,esk3_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k7_relat_1(X1,X2) = k5_relat_1(k6_relat_1(X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_27,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | r1_tarski(k2_relat_1(k7_relat_1(X18,X17)),k2_relat_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

cnf(c_0_30,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,X1),X2) = k7_relat_1(esk3_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_16])])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(k5_relat_1(k6_relat_1(X1),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( k5_relat_1(k6_relat_1(X1),esk3_0) = k7_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_16])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_16])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,esk1_0)) = k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk3_0,X1)) = k9_relat_1(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk3_0,X1)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk1_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_41]),c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___107_C00_02_nc_F1_PI_AE_Q4_CS_SP_PS_S00EN
% 0.13/0.38  # and selection function PSelectSmallestOrientable.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.026 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 0.13/0.38  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.13/0.38  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 0.13/0.38  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 0.13/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.13/0.38  fof(t94_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k5_relat_1(k6_relat_1(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 0.13/0.38  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.13/0.38  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.13/0.38  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.13/0.38  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 0.13/0.38  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.13/0.38  fof(c_0_11, plain, ![X7, X8]:(~v1_relat_1(X7)|~v1_relat_1(X8)|v1_relat_1(k5_relat_1(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k2_relat_1(esk3_0)))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X10, X11, X12]:(~v1_relat_1(X12)|(~r1_tarski(X10,X11)|k7_relat_1(k7_relat_1(X12,X11),X10)=k7_relat_1(X12,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.13/0.38  fof(c_0_14, plain, ![X21, X22]:(~v1_relat_1(X22)|~v1_funct_1(X22)|(~r1_tarski(X21,k2_relat_1(X22))|k9_relat_1(X22,k10_relat_1(X22,X21))=X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.13/0.38  cnf(c_0_15, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  fof(c_0_17, plain, ![X9]:v1_relat_1(k6_relat_1(X9)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.13/0.38  fof(c_0_18, plain, ![X15, X16]:(~v1_relat_1(X16)|k7_relat_1(X16,X15)=k5_relat_1(k6_relat_1(X15),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_relat_1])])).
% 0.13/0.38  fof(c_0_19, plain, ![X19, X20]:(~v1_relat_1(X20)|~v1_funct_1(X20)|r1_tarski(k9_relat_1(X20,k10_relat_1(X20,X19)),X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.13/0.38  cnf(c_0_20, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_21, plain, ![X13, X14]:(~v1_relat_1(X14)|k2_relat_1(k7_relat_1(X14,X13))=k9_relat_1(X14,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.13/0.38  cnf(c_0_22, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (v1_relat_1(k5_relat_1(X1,esk3_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.38  cnf(c_0_25, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.38  cnf(c_0_26, plain, (k7_relat_1(X1,X2)=k5_relat_1(k6_relat_1(X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.38  fof(c_0_27, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.13/0.38  cnf(c_0_28, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  fof(c_0_29, plain, ![X17, X18]:(~v1_relat_1(X18)|r1_tarski(k2_relat_1(k7_relat_1(X18,X17)),k2_relat_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,X1),X2)=k7_relat_1(esk3_0,X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_32, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_16])])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (v1_relat_1(k5_relat_1(k6_relat_1(X1),esk3_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (k5_relat_1(k6_relat_1(X1),esk3_0)=k7_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_26, c_0_16])).
% 0.13/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_16])])).
% 0.13/0.38  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (k7_relat_1(k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)),k10_relat_1(esk3_0,esk1_0))=k7_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k2_relat_1(k7_relat_1(esk3_0,X1))=k9_relat_1(esk3_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_16])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0))=esk1_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  cnf(c_0_43, negated_conjecture, (v1_relat_1(k7_relat_1(esk3_0,X1))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,X2)|~r1_tarski(X1,k9_relat_1(esk3_0,k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(esk1_0,k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_41]), c_0_43])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 48
% 0.13/0.38  # Proof object clause steps            : 27
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 21
% 0.13/0.38  # Proof object clause conjectures      : 18
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 14
% 0.13/0.38  # Proof object initial formulas used   : 10
% 0.13/0.38  # Proof object generating inferences   : 12
% 0.13/0.38  # Proof object simplifying inferences  : 11
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 10
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 14
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 14
% 0.13/0.38  # Processed clauses                    : 150
% 0.13/0.38  # ...of these trivial                  : 14
% 0.13/0.38  # ...subsumed                          : 4
% 0.13/0.38  # ...remaining for further processing  : 132
% 0.13/0.38  # Other redundant clauses eliminated   : 0
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 8
% 0.13/0.38  # Generated clauses                    : 928
% 0.13/0.38  # ...of the previous two non-trivial   : 884
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 928
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
% 0.13/0.38  # Current number of processed clauses  : 110
% 0.13/0.38  #    Positive orientable unit clauses  : 78
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 31
% 0.13/0.38  # Current number of unprocessed clauses: 743
% 0.13/0.38  # ...number of literals in the above   : 833
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 22
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 60
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 49
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 4
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 82
% 0.13/0.38  # BW rewrite match successes           : 7
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 15380
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.040 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
