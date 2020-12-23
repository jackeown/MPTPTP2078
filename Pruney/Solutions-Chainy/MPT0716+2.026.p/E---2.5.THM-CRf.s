%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:46 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 182 expanded)
%              Number of clauses        :   28 (  75 expanded)
%              Number of leaves         :    7 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 849 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   11 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t171_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
            <=> ( r1_tarski(X3,k1_relat_1(X1))
                & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))
              <=> ( r1_tarski(X3,k1_relat_1(X1))
                  & r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t171_funct_1])).

fof(c_0_8,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_relat_1(X13)
      | k1_relat_1(k5_relat_1(X12,X13)) = k10_relat_1(X12,k1_relat_1(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_9,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
      | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
      | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) )
    & ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
      | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) )
    & ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
      | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X11)
      | r1_tarski(k10_relat_1(X11,X10),k1_relat_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_11,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk1_0,X1),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_relat_1(esk2_0)) = k1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_12])])).

fof(c_0_23,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_27,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk1_0))
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k9_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_27,c_0_12])).

fof(c_0_32,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r1_tarski(X16,k1_relat_1(X18))
      | ~ r1_tarski(k9_relat_1(X18,X16),X17)
      | r1_tarski(X16,k10_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(esk2_0))
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk3_0,k10_relat_1(esk1_0,X1))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_18]),c_0_12])])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_39]),c_0_21]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.19/0.42  # and selection function PSelectMinOptimalNoXTypePred.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.027 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 0.19/0.42  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 0.19/0.42  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 0.19/0.42  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 0.19/0.42  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.19/0.42  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 0.19/0.42  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 0.19/0.42  fof(c_0_7, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.19/0.42  fof(c_0_8, plain, ![X12, X13]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|k1_relat_1(k5_relat_1(X12,X13))=k10_relat_1(X12,k1_relat_1(X13)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.19/0.42  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|(~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))))&((r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))&(r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.19/0.42  fof(c_0_10, plain, ![X10, X11]:(~v1_relat_1(X11)|r1_tarski(k10_relat_1(X11,X10),k1_relat_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.19/0.42  cnf(c_0_11, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.42  cnf(c_0_12, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.42  fof(c_0_13, plain, ![X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.19/0.42  cnf(c_0_14, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.42  cnf(c_0_15, negated_conjecture, (k10_relat_1(esk1_0,k1_relat_1(X1))=k1_relat_1(k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.42  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.42  cnf(c_0_17, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.42  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.42  fof(c_0_19, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.19/0.42  cnf(c_0_20, negated_conjecture, (r1_tarski(k10_relat_1(esk1_0,X1),k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_14, c_0_12])).
% 0.19/0.42  cnf(c_0_21, negated_conjecture, (k10_relat_1(esk1_0,k1_relat_1(esk2_0))=k1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.42  cnf(c_0_22, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_12])])).
% 0.19/0.42  fof(c_0_23, plain, ![X7, X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(X7,X8)|r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.19/0.42  cnf(c_0_24, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_25, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.19/0.42  cnf(c_0_27, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.42  cnf(c_0_28, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk1_0))|~r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.42  cnf(c_0_29, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.42  cnf(c_0_30, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk2_0))|~r1_tarski(X1,k9_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))), inference(spm,[status(thm)],[c_0_24, c_0_26])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_27, c_0_12])).
% 0.19/0.42  fof(c_0_32, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r1_tarski(X16,k1_relat_1(X18))|~r1_tarski(k9_relat_1(X18,X16),X17)|r1_tarski(X16,k10_relat_1(X18,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.42  cnf(c_0_34, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.42  cnf(c_0_35, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,X1),k1_relat_1(esk2_0))|~r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.42  cnf(c_0_36, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.42  cnf(c_0_37, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (r1_tarski(esk3_0,k10_relat_1(esk1_0,X1))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_18]), c_0_12])])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.19/0.42  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_39]), c_0_21]), c_0_41]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 43
% 0.19/0.42  # Proof object clause steps            : 28
% 0.19/0.42  # Proof object formula steps           : 15
% 0.19/0.42  # Proof object conjectures             : 25
% 0.19/0.42  # Proof object clause conjectures      : 22
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 12
% 0.19/0.42  # Proof object initial formulas used   : 7
% 0.19/0.42  # Proof object generating inferences   : 14
% 0.19/0.42  # Proof object simplifying inferences  : 11
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 7
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 13
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 13
% 0.19/0.42  # Processed clauses                    : 359
% 0.19/0.42  # ...of these trivial                  : 5
% 0.19/0.42  # ...subsumed                          : 103
% 0.19/0.42  # ...remaining for further processing  : 251
% 0.19/0.42  # Other redundant clauses eliminated   : 0
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 51
% 0.19/0.42  # Backward-rewritten                   : 15
% 0.19/0.42  # Generated clauses                    : 2265
% 0.19/0.42  # ...of the previous two non-trivial   : 2173
% 0.19/0.42  # Contextual simplify-reflections      : 1
% 0.19/0.42  # Paramodulations                      : 2265
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 0
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 172
% 0.19/0.42  #    Positive orientable unit clauses  : 84
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 86
% 0.19/0.42  # Current number of unprocessed clauses: 1753
% 0.19/0.42  # ...number of literals in the above   : 7847
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 79
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 4599
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 2965
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 152
% 0.19/0.42  # Unit Clause-clause subsumption calls : 68
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 118
% 0.19/0.42  # BW rewrite match successes           : 2
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 48006
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.074 s
% 0.19/0.42  # System time              : 0.012 s
% 0.19/0.42  # Total time               : 0.086 s
% 0.19/0.42  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
