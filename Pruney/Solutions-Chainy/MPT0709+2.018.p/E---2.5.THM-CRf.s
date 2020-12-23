%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:32 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 230 expanded)
%              Number of clauses        :   36 (  85 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 797 expanded)
%              Number of equality atoms :   31 ( 159 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t154_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,X1) = k10_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(t146_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(t155_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( v2_funct_1(X2)
       => k10_relat_1(X2,X1) = k9_relat_1(k2_funct_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(t147_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,k2_relat_1(X2))
       => k9_relat_1(X2,k10_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( ( r1_tarski(X1,k1_relat_1(X2))
            & v2_funct_1(X2) )
         => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_1])).

fof(c_0_11,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X28] :
      ( ( v1_relat_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(esk1_0,k1_relat_1(esk2_0))
    & v2_funct_1(esk2_0)
    & k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

fof(c_0_14,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ v1_funct_1(X37)
      | ~ v2_funct_1(X37)
      | k9_relat_1(X37,X36) = k10_relat_1(k2_funct_1(X37),X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).

fof(c_0_15,plain,(
    ! [X32,X33] :
      ( ~ v1_relat_1(X33)
      | ~ r1_tarski(X32,k1_relat_1(X33))
      | r1_tarski(X32,k10_relat_1(X33,k9_relat_1(X33,X32))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k9_relat_1(X18,k1_relat_1(X18)) = k2_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

fof(c_0_19,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ v2_funct_1(X39)
      | k10_relat_1(X39,X38) = k9_relat_1(k2_funct_1(X39),X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k9_relat_1(X1,X2) = k10_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,X2) = k9_relat_1(k2_funct_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_30,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_relat_1(X27)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(k10_relat_1(X27,X25),k10_relat_1(X27,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_32,negated_conjecture,
    ( k10_relat_1(k2_funct_1(esk2_0),X1) = k9_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_21]),c_0_22])])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(esk2_0,k1_relat_1(esk2_0)) = k2_relat_1(esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_22])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk2_0),X1) = k10_relat_1(esk2_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_22]),c_0_24]),c_0_21])])).

cnf(c_0_38,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk2_0,X1),k1_relat_1(k2_funct_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k2_relat_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(esk2_0) = k10_relat_1(esk2_0,X1)
    | ~ r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( k10_relat_1(esk2_0,k1_relat_1(k2_funct_1(esk2_0))) = k2_relat_1(k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_31]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k2_funct_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k10_relat_1(esk2_0,k2_relat_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_40]),c_0_36])])).

fof(c_0_46,plain,(
    ! [X34,X35] :
      ( ~ v1_relat_1(X35)
      | ~ v1_funct_1(X35)
      | ~ r1_tarski(X34,k2_relat_1(X35))
      | k9_relat_1(X35,k10_relat_1(X35,X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).

cnf(c_0_47,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk2_0)) = k1_relat_1(esk2_0)
    | ~ r1_tarski(k1_relat_1(esk2_0),k2_relat_1(k2_funct_1(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k2_relat_1(k2_funct_1(esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_42])).

cnf(c_0_50,plain,
    ( k9_relat_1(X1,k10_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k2_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_22]),c_0_21])])).

cnf(c_0_52,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk2_0)) = k1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1)) = X1
    | ~ r1_tarski(X1,k1_relat_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_51])]),c_0_32]),c_0_37]),c_0_52])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S05DN
% 0.13/0.40  # and selection function SelectDivLits.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.045 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t164_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.40  fof(t154_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k9_relat_1(X2,X1)=k10_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_funct_1)).
% 0.13/0.40  fof(t146_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>r1_tarski(X1,k10_relat_1(X2,k9_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 0.13/0.40  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.13/0.40  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.13/0.40  fof(t155_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v2_funct_1(X2)=>k10_relat_1(X2,X1)=k9_relat_1(k2_funct_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 0.13/0.40  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 0.13/0.40  fof(t147_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(X1,k2_relat_1(X2))=>k9_relat_1(X2,k10_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 0.13/0.40  fof(c_0_10, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1))), inference(assume_negation,[status(cth)],[t164_funct_1])).
% 0.13/0.40  fof(c_0_11, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  fof(c_0_12, plain, ![X28]:((v1_relat_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.40  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&((r1_tarski(esk1_0,k1_relat_1(esk2_0))&v2_funct_1(esk2_0))&k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.13/0.40  fof(c_0_14, plain, ![X36, X37]:(~v1_relat_1(X37)|~v1_funct_1(X37)|(~v2_funct_1(X37)|k9_relat_1(X37,X36)=k10_relat_1(k2_funct_1(X37),X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t154_funct_1])])).
% 0.13/0.40  fof(c_0_15, plain, ![X32, X33]:(~v1_relat_1(X33)|(~r1_tarski(X32,k1_relat_1(X33))|r1_tarski(X32,k10_relat_1(X33,k9_relat_1(X33,X32))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_funct_1])])).
% 0.13/0.40  cnf(c_0_16, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  fof(c_0_17, plain, ![X18]:(~v1_relat_1(X18)|k9_relat_1(X18,k1_relat_1(X18))=k2_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.13/0.40  fof(c_0_18, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 0.13/0.40  fof(c_0_19, plain, ![X38, X39]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~v2_funct_1(X39)|k10_relat_1(X39,X38)=k9_relat_1(k2_funct_1(X39),X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t155_funct_1])])).
% 0.13/0.40  cnf(c_0_20, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_21, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_23, plain, (k9_relat_1(X1,X2)=k10_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_25, plain, (r1_tarski(X2,k10_relat_1(X1,k9_relat_1(X1,X2)))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_27, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_28, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_29, plain, (k10_relat_1(X1,X2)=k9_relat_1(k2_funct_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  fof(c_0_30, plain, ![X25, X26, X27]:(~v1_relat_1(X27)|(~r1_tarski(X25,X26)|r1_tarski(k10_relat_1(X27,X25),k10_relat_1(X27,X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (k10_relat_1(k2_funct_1(esk2_0),X1)=k9_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_21]), c_0_22])])).
% 0.13/0.40  cnf(c_0_33, plain, (r1_tarski(k1_relat_1(X1),k10_relat_1(X1,k9_relat_1(X1,k1_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (k9_relat_1(esk2_0,k1_relat_1(esk2_0))=k2_relat_1(esk2_0)), inference(spm,[status(thm)],[c_0_27, c_0_22])).
% 0.13/0.40  cnf(c_0_35, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k1_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (k9_relat_1(k2_funct_1(esk2_0),X1)=k10_relat_1(esk2_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_22]), c_0_24]), c_0_21])])).
% 0.13/0.40  cnf(c_0_38, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (r1_tarski(k9_relat_1(esk2_0,X1),k1_relat_1(k2_funct_1(esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_31]), c_0_32])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,k2_relat_1(esk2_0)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_34])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (k1_relat_1(esk2_0)=k10_relat_1(esk2_0,X1)|~r1_tarski(k1_relat_1(esk2_0),k10_relat_1(esk2_0,X1))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (k10_relat_1(esk2_0,k1_relat_1(k2_funct_1(esk2_0)))=k2_relat_1(k2_funct_1(esk2_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_31]), c_0_37])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (r1_tarski(k10_relat_1(esk2_0,X1),k10_relat_1(esk2_0,X2))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k1_relat_1(k2_funct_1(esk2_0)))), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (k10_relat_1(esk2_0,k2_relat_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_40]), c_0_36])])).
% 0.13/0.40  fof(c_0_46, plain, ![X34, X35]:(~v1_relat_1(X35)|~v1_funct_1(X35)|(~r1_tarski(X34,k2_relat_1(X35))|k9_relat_1(X35,k10_relat_1(X35,X34))=X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_funct_1])])).
% 0.13/0.40  cnf(c_0_47, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (k2_relat_1(k2_funct_1(esk2_0))=k1_relat_1(esk2_0)|~r1_tarski(k1_relat_1(esk2_0),k2_relat_1(k2_funct_1(esk2_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k2_relat_1(k2_funct_1(esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_42])).
% 0.13/0.40  cnf(c_0_50, plain, (k9_relat_1(X1,k10_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k2_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (v1_funct_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_22]), c_0_21])])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (k2_relat_1(k2_funct_1(esk2_0))=k1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.13/0.40  cnf(c_0_53, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,X1))=X1|~r1_tarski(X1,k1_relat_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_31]), c_0_51])]), c_0_32]), c_0_37]), c_0_52])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (k10_relat_1(esk2_0,k9_relat_1(esk2_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 57
% 0.13/0.40  # Proof object clause steps            : 36
% 0.13/0.40  # Proof object formula steps           : 21
% 0.13/0.40  # Proof object conjectures             : 26
% 0.13/0.40  # Proof object clause conjectures      : 23
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 16
% 0.13/0.40  # Proof object initial formulas used   : 10
% 0.13/0.40  # Proof object generating inferences   : 18
% 0.13/0.40  # Proof object simplifying inferences  : 26
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 21
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 28
% 0.13/0.40  # Removed in clause preprocessing      : 3
% 0.13/0.40  # Initial clauses in saturation        : 25
% 0.13/0.40  # Processed clauses                    : 143
% 0.13/0.40  # ...of these trivial                  : 1
% 0.13/0.40  # ...subsumed                          : 11
% 0.13/0.40  # ...remaining for further processing  : 131
% 0.13/0.40  # Other redundant clauses eliminated   : 2
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 15
% 0.13/0.40  # Generated clauses                    : 236
% 0.13/0.40  # ...of the previous two non-trivial   : 199
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 234
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 2
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 90
% 0.13/0.40  #    Positive orientable unit clauses  : 48
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 40
% 0.13/0.40  # Current number of unprocessed clauses: 95
% 0.13/0.40  # ...number of literals in the above   : 124
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 42
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 105
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 99
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 11
% 0.13/0.40  # Unit Clause-clause subsumption calls : 2
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 71
% 0.13/0.40  # BW rewrite match successes           : 6
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 6394
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.055 s
% 0.13/0.40  # System time              : 0.006 s
% 0.13/0.40  # Total time               : 0.062 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
