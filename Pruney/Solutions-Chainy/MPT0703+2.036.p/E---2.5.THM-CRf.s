%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:18 EST 2020

% Result     : Theorem 0.22s
% Output     : CNFRefutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 115 expanded)
%              Number of clauses        :   31 (  48 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 351 expanded)
%              Number of equality atoms :   21 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(t176_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t151_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k3_xboole_0(X1,k10_relat_1(X3,X2)),k10_relat_1(X3,k3_xboole_0(k9_relat_1(X3,X1),X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_funct_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t145_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))
            & r1_tarski(X1,k2_relat_1(X3)) )
         => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t158_funct_1])).

fof(c_0_11,plain,(
    ! [X26,X27,X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(k10_relat_1(X28,k3_xboole_0(X26,X27)),k3_xboole_0(k10_relat_1(X28,X26),k10_relat_1(X28,X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_relat_1])])).

fof(c_0_12,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))
    & r1_tarski(esk1_0,k2_relat_1(esk3_0))
    & ~ r1_tarski(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_13,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k3_xboole_0(X16,X17) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_14,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | ~ v1_funct_1(X34)
      | ~ r1_tarski(X33,k2_relat_1(X34))
      | k9_relat_1(X34,k10_relat_1(X34,X33)) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_16,plain,
    ( r1_tarski(k10_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | r1_tarski(k3_xboole_0(X35,k10_relat_1(X37,X36)),k10_relat_1(X37,k3_xboole_0(k9_relat_1(X37,X35),X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_funct_1])])).

cnf(c_0_21,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k2_xboole_0(X9,X10) = X10 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0)) = k10_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(k3_xboole_0(X2,k10_relat_1(X1,X3)),k10_relat_1(X1,k3_xboole_0(k9_relat_1(X1,X2),X3)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)) = X1
    | ~ r1_tarski(X1,k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk1_0,k2_relat_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_30,plain,(
    ! [X18,X19,X20] : r1_tarski(k2_xboole_0(k3_xboole_0(X18,X19),k3_xboole_0(X18,X20)),k2_xboole_0(X19,X20)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | r1_tarski(k9_relat_1(X30,k10_relat_1(X30,X29)),X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k10_relat_1(esk3_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,k3_xboole_0(k9_relat_1(esk3_0,X1),X2))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0)) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_38,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | ~ r1_tarski(X14,X15)
      | r1_tarski(X13,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)) = k10_relat_1(esk3_0,esk1_0)
    | ~ r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_37])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_22]),c_0_17])])).

cnf(c_0_47,negated_conjecture,
    ( k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)) = k10_relat_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:06:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  # Version: 2.5pre002
% 0.15/0.35  # No SInE strategy applied
% 0.15/0.35  # Trying AutoSched0 for 299 seconds
% 0.22/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S02AI
% 0.22/0.41  # and selection function SelectNonStrongRROptimalLit.
% 0.22/0.41  #
% 0.22/0.41  # Preprocessing time       : 0.036 s
% 0.22/0.41  # Presaturation interreduction done
% 0.22/0.41  
% 0.22/0.41  # Proof found!
% 0.22/0.41  # SZS status Theorem
% 0.22/0.41  # SZS output start CNFRefutation
% 0.22/0.41  fof(t158_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 0.22/0.41  fof(t176_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 0.22/0.41  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.22/0.41  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.22/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.22/0.41  fof(t151_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k3_xboole_0(X1,k10_relat_1(X3,X2)),k10_relat_1(X3,k3_xboole_0(k9_relat_1(X3,X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_funct_1)).
% 0.22/0.41  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.22/0.41  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 0.22/0.41  fof(t145_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>r1_tarski(k9_relat_1(X2,k10_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 0.22/0.41  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.22/0.41  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2))&r1_tarski(X1,k2_relat_1(X3)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t158_funct_1])).
% 0.22/0.41  fof(c_0_11, plain, ![X26, X27, X28]:(~v1_relat_1(X28)|r1_tarski(k10_relat_1(X28,k3_xboole_0(X26,X27)),k3_xboole_0(k10_relat_1(X28,X26),k10_relat_1(X28,X27)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_relat_1])])).
% 0.22/0.41  fof(c_0_12, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))&r1_tarski(esk1_0,k2_relat_1(esk3_0)))&~r1_tarski(esk1_0,esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.22/0.41  fof(c_0_13, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k3_xboole_0(X16,X17)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.22/0.41  fof(c_0_14, plain, ![X33, X34]:(~v1_relat_1(X34)|~v1_funct_1(X34)|(~r1_tarski(X33,k2_relat_1(X34))|k9_relat_1(X34,k10_relat_1(X34,X33))=X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.22/0.41  fof(c_0_15, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.22/0.41  cnf(c_0_16, plain, (r1_tarski(k10_relat_1(X1,k3_xboole_0(X2,X3)),k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.22/0.41  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  cnf(c_0_18, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.22/0.41  cnf(c_0_19, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  fof(c_0_20, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|r1_tarski(k3_xboole_0(X35,k10_relat_1(X37,X36)),k10_relat_1(X37,k3_xboole_0(k9_relat_1(X37,X35),X36)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_funct_1])])).
% 0.22/0.41  cnf(c_0_21, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.22/0.41  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  fof(c_0_23, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k2_xboole_0(X9,X10)=X10), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.22/0.41  cnf(c_0_24, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.41  cnf(c_0_25, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2)))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.22/0.41  cnf(c_0_26, negated_conjecture, (k3_xboole_0(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,esk2_0))=k10_relat_1(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.22/0.41  cnf(c_0_27, plain, (r1_tarski(k3_xboole_0(X2,k10_relat_1(X1,X3)),k10_relat_1(X1,k3_xboole_0(k9_relat_1(X1,X2),X3)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.22/0.41  cnf(c_0_28, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1))=X1|~r1_tarski(X1,k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_17])])).
% 0.22/0.41  cnf(c_0_29, negated_conjecture, (r1_tarski(esk1_0,k2_relat_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  fof(c_0_30, plain, ![X18, X19, X20]:r1_tarski(k2_xboole_0(k3_xboole_0(X18,X19),k3_xboole_0(X18,X20)),k2_xboole_0(X19,X20)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 0.22/0.41  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.22/0.41  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.22/0.41  fof(c_0_33, plain, ![X29, X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|r1_tarski(k9_relat_1(X30,k10_relat_1(X30,X29)),X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t145_funct_1])])).
% 0.22/0.41  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.22/0.41  cnf(c_0_35, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)),k10_relat_1(esk3_0,esk1_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.22/0.41  cnf(c_0_36, negated_conjecture, (r1_tarski(k3_xboole_0(X1,k10_relat_1(esk3_0,X2)),k10_relat_1(esk3_0,k3_xboole_0(k9_relat_1(esk3_0,X1),X2)))), inference(spm,[status(thm)],[c_0_27, c_0_17])).
% 0.22/0.41  cnf(c_0_37, negated_conjecture, (k9_relat_1(esk3_0,k10_relat_1(esk3_0,esk1_0))=esk1_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.22/0.41  fof(c_0_38, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|~r1_tarski(X14,X15)|r1_tarski(X13,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.22/0.41  cnf(c_0_39, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.22/0.41  cnf(c_0_40, plain, (k2_xboole_0(X1,X1)=X1), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.22/0.41  cnf(c_0_41, plain, (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X2)),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.22/0.41  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0))=k10_relat_1(esk3_0,esk1_0)|~r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.22/0.41  cnf(c_0_43, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,esk1_0),k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_37])).
% 0.22/0.41  cnf(c_0_44, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.22/0.41  cnf(c_0_45, plain, (r1_tarski(k3_xboole_0(X1,X2),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_40])).
% 0.22/0.41  cnf(c_0_46, negated_conjecture, (r1_tarski(k9_relat_1(esk3_0,k10_relat_1(esk3_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_22]), c_0_17])])).
% 0.22/0.41  cnf(c_0_47, negated_conjecture, (k10_relat_1(esk3_0,k3_xboole_0(esk1_0,esk2_0))=k10_relat_1(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_43])])).
% 0.22/0.41  cnf(c_0_48, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k3_xboole_0(X3,X2))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.22/0.41  cnf(c_0_49, negated_conjecture, (r1_tarski(esk1_0,k3_xboole_0(esk1_0,esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_37])).
% 0.22/0.41  cnf(c_0_50, negated_conjecture, (~r1_tarski(esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.22/0.41  cnf(c_0_51, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), ['proof']).
% 0.22/0.41  # SZS output end CNFRefutation
% 0.22/0.41  # Proof object total steps             : 52
% 0.22/0.41  # Proof object clause steps            : 31
% 0.22/0.41  # Proof object formula steps           : 21
% 0.22/0.41  # Proof object conjectures             : 20
% 0.22/0.41  # Proof object clause conjectures      : 17
% 0.22/0.41  # Proof object formula conjectures     : 3
% 0.22/0.41  # Proof object initial clauses used    : 15
% 0.22/0.41  # Proof object initial formulas used   : 10
% 0.22/0.41  # Proof object generating inferences   : 14
% 0.22/0.41  # Proof object simplifying inferences  : 11
% 0.22/0.41  # Training examples: 0 positive, 0 negative
% 0.22/0.41  # Parsed axioms                        : 16
% 0.22/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.22/0.41  # Initial clauses                      : 22
% 0.22/0.41  # Removed in clause preprocessing      : 0
% 0.22/0.41  # Initial clauses in saturation        : 22
% 0.22/0.41  # Processed clauses                    : 312
% 0.22/0.41  # ...of these trivial                  : 15
% 0.22/0.41  # ...subsumed                          : 96
% 0.22/0.41  # ...remaining for further processing  : 201
% 0.22/0.41  # Other redundant clauses eliminated   : 2
% 0.22/0.41  # Clauses deleted for lack of memory   : 0
% 0.22/0.41  # Backward-subsumed                    : 0
% 0.22/0.41  # Backward-rewritten                   : 10
% 0.22/0.41  # Generated clauses                    : 1471
% 0.22/0.41  # ...of the previous two non-trivial   : 1169
% 0.22/0.41  # Contextual simplify-reflections      : 0
% 0.22/0.41  # Paramodulations                      : 1469
% 0.22/0.41  # Factorizations                       : 0
% 0.22/0.41  # Equation resolutions                 : 2
% 0.22/0.41  # Propositional unsat checks           : 0
% 0.22/0.41  #    Propositional check models        : 0
% 0.22/0.41  #    Propositional check unsatisfiable : 0
% 0.22/0.41  #    Propositional clauses             : 0
% 0.22/0.41  #    Propositional clauses after purity: 0
% 0.22/0.41  #    Propositional unsat core size     : 0
% 0.22/0.41  #    Propositional preprocessing time  : 0.000
% 0.22/0.41  #    Propositional encoding time       : 0.000
% 0.22/0.41  #    Propositional solver time         : 0.000
% 0.22/0.41  #    Success case prop preproc time    : 0.000
% 0.22/0.41  #    Success case prop encoding time   : 0.000
% 0.22/0.41  #    Success case prop solver time     : 0.000
% 0.22/0.41  # Current number of processed clauses  : 168
% 0.22/0.41  #    Positive orientable unit clauses  : 64
% 0.22/0.41  #    Positive unorientable unit clauses: 0
% 0.22/0.41  #    Negative unit clauses             : 1
% 0.22/0.41  #    Non-unit-clauses                  : 103
% 0.22/0.41  # Current number of unprocessed clauses: 884
% 0.22/0.41  # ...number of literals in the above   : 1120
% 0.22/0.41  # Current number of archived formulas  : 0
% 0.22/0.41  # Current number of archived clauses   : 31
% 0.22/0.41  # Clause-clause subsumption calls (NU) : 2222
% 0.22/0.41  # Rec. Clause-clause subsumption calls : 2011
% 0.22/0.41  # Non-unit clause-clause subsumptions  : 96
% 0.22/0.41  # Unit Clause-clause subsumption calls : 50
% 0.22/0.41  # Rewrite failures with RHS unbound    : 0
% 0.22/0.41  # BW rewrite match attempts            : 48
% 0.22/0.41  # BW rewrite match successes           : 4
% 0.22/0.41  # Condensation attempts                : 0
% 0.22/0.41  # Condensation successes               : 0
% 0.22/0.41  # Termbank termtop insertions          : 18318
% 0.22/0.41  
% 0.22/0.41  # -------------------------------------------------
% 0.22/0.41  # User time                : 0.057 s
% 0.22/0.41  # System time              : 0.006 s
% 0.22/0.41  # Total time               : 0.064 s
% 0.22/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
