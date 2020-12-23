%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:46 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 171 expanded)
%              Number of clauses        :   27 (  68 expanded)
%              Number of leaves         :    7 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  117 ( 838 expanded)
%              Number of equality atoms :    5 (  15 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

fof(t44_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t163_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_tarski(X1,k1_relat_1(X3))
          & r1_tarski(k9_relat_1(X3,X1),X2) )
       => r1_tarski(X1,k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t156_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

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
      | r1_tarski(k1_relat_1(k5_relat_1(X12,X13)),k1_relat_1(X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).

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

cnf(c_0_10,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X4,X5,X6] :
      ( ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X6)
      | r1_tarski(X4,X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk1_0,X1)),k1_relat_1(esk1_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ v1_relat_1(X11)
      | k1_relat_1(k5_relat_1(X10,X11)) = k10_relat_1(X10,k1_relat_1(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

fof(c_0_18,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ v1_funct_1(X18)
      | ~ r1_tarski(X16,k1_relat_1(X18))
      | ~ r1_tarski(k9_relat_1(X18,X16),X17)
      | r1_tarski(X16,k10_relat_1(X18,X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk1_0))
    | ~ r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(esk1_0,X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(esk3_0,k1_relat_1(esk1_0))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,k10_relat_1(esk1_0,X1))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_11])])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(esk1_0,k1_relat_1(esk2_0)) = k1_relat_1(k5_relat_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))
    | r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))
    | ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_23])])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_32,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_34,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_35,plain,(
    ! [X7,X8,X9] :
      ( ~ v1_relat_1(X9)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),X1)
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_11])])).

cnf(c_0_38,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk1_0,esk3_0),k9_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_11])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:01:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S01BI
% 0.12/0.39  # and selection function PSelectMinOptimalNoXTypePred.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.029 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t171_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 0.12/0.39  fof(t44_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 0.12/0.39  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.12/0.39  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.12/0.39  fof(t163_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(X1,k1_relat_1(X3))&r1_tarski(k9_relat_1(X3,X1),X2))=>r1_tarski(X1,k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 0.12/0.39  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.12/0.39  fof(t156_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 0.12/0.39  fof(c_0_7, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:(r1_tarski(X3,k1_relat_1(k5_relat_1(X1,X2)))<=>(r1_tarski(X3,k1_relat_1(X1))&r1_tarski(k9_relat_1(X1,X3),k1_relat_1(X2))))))), inference(assume_negation,[status(cth)],[t171_funct_1])).
% 0.12/0.39  fof(c_0_8, plain, ![X12, X13]:(~v1_relat_1(X12)|(~v1_relat_1(X13)|r1_tarski(k1_relat_1(k5_relat_1(X12,X13)),k1_relat_1(X12)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_relat_1])])])).
% 0.12/0.39  fof(c_0_9, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|(~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))))&((r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))&(r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.12/0.39  cnf(c_0_10, plain, (r1_tarski(k1_relat_1(k5_relat_1(X1,X2)),k1_relat_1(X1))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  fof(c_0_12, plain, ![X4, X5, X6]:(~r1_tarski(X4,X5)|~r1_tarski(X5,X6)|r1_tarski(X4,X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.12/0.39  cnf(c_0_13, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk1_0,X1)),k1_relat_1(esk1_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_15, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.39  cnf(c_0_16, negated_conjecture, (r1_tarski(k1_relat_1(k5_relat_1(esk1_0,esk2_0)),k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.39  fof(c_0_17, plain, ![X10, X11]:(~v1_relat_1(X10)|(~v1_relat_1(X11)|k1_relat_1(k5_relat_1(X10,X11))=k10_relat_1(X10,k1_relat_1(X11)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.12/0.39  fof(c_0_18, plain, ![X16, X17, X18]:(~v1_relat_1(X18)|~v1_funct_1(X18)|(~r1_tarski(X16,k1_relat_1(X18))|~r1_tarski(k9_relat_1(X18,X16),X17)|r1_tarski(X16,k10_relat_1(X18,X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t163_funct_1])])).
% 0.12/0.39  cnf(c_0_19, negated_conjecture, (r1_tarski(X1,k1_relat_1(esk1_0))|~r1_tarski(X1,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_21, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_22, plain, (r1_tarski(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k9_relat_1(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (k10_relat_1(esk1_0,k1_relat_1(X1))=k1_relat_1(k5_relat_1(esk1_0,X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_11])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(esk3_0,k1_relat_1(esk1_0))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,k10_relat_1(esk1_0,X1))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_11])])).
% 0.12/0.39  cnf(c_0_28, negated_conjecture, (k10_relat_1(esk1_0,k1_relat_1(esk2_0))=k1_relat_1(k5_relat_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_25, c_0_14])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))|r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_30, negated_conjecture, (~r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))|~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_23])])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (r1_tarski(esk3_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.12/0.39  fof(c_0_32, plain, ![X14, X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|r1_tarski(k9_relat_1(X15,k10_relat_1(X15,X14)),X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,esk3_0),k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 0.12/0.39  cnf(c_0_34, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.39  fof(c_0_35, plain, ![X7, X8, X9]:(~v1_relat_1(X9)|(~r1_tarski(X7,X8)|r1_tarski(k9_relat_1(X9,X7),k9_relat_1(X9,X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t156_relat_1])])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,esk3_0),X1)|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_33, c_0_15])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,k10_relat_1(esk1_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_24]), c_0_11])])).
% 0.12/0.39  cnf(c_0_38, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.12/0.39  cnf(c_0_39, negated_conjecture, (~r1_tarski(k9_relat_1(esk1_0,esk3_0),k9_relat_1(esk1_0,k1_relat_1(k5_relat_1(esk1_0,esk2_0))))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (r1_tarski(k9_relat_1(esk1_0,X1),k9_relat_1(esk1_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_11])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_31])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 42
% 0.12/0.39  # Proof object clause steps            : 27
% 0.12/0.39  # Proof object formula steps           : 15
% 0.12/0.39  # Proof object conjectures             : 24
% 0.12/0.39  # Proof object clause conjectures      : 21
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 12
% 0.12/0.39  # Proof object initial formulas used   : 7
% 0.12/0.39  # Proof object generating inferences   : 13
% 0.12/0.39  # Proof object simplifying inferences  : 13
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 7
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 13
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 13
% 0.12/0.39  # Processed clauses                    : 167
% 0.12/0.39  # ...of these trivial                  : 1
% 0.12/0.39  # ...subsumed                          : 21
% 0.12/0.39  # ...remaining for further processing  : 145
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 39
% 0.12/0.39  # Backward-rewritten                   : 5
% 0.12/0.39  # Generated clauses                    : 502
% 0.12/0.39  # ...of the previous two non-trivial   : 489
% 0.12/0.39  # Contextual simplify-reflections      : 2
% 0.12/0.39  # Paramodulations                      : 500
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 0
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 86
% 0.12/0.39  #    Positive orientable unit clauses  : 37
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 5
% 0.12/0.39  #    Non-unit-clauses                  : 44
% 0.12/0.39  # Current number of unprocessed clauses: 314
% 0.12/0.39  # ...number of literals in the above   : 1102
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 59
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1330
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 790
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 57
% 0.12/0.39  # Unit Clause-clause subsumption calls : 36
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 30
% 0.12/0.39  # BW rewrite match successes           : 3
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 11327
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.046 s
% 0.12/0.39  # System time              : 0.003 s
% 0.12/0.39  # Total time               : 0.049 s
% 0.12/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
