%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:33 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  79 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  111 ( 203 expanded)
%              Number of equality atoms :   13 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(t141_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_xboole_0(X2,X3)
         => r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

fof(t178_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(t55_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( r1_xboole_0(k2_tarski(X1,X2),X3)
        & r2_hidden(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t137_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => k10_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

fof(c_0_9,plain,(
    ! [X22,X23] :
      ( ( k10_relat_1(X23,X22) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X23),X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_xboole_0(k2_relat_1(X23),X22)
        | k10_relat_1(X23,X22) = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

fof(c_0_10,plain,(
    ! [X16] : r1_xboole_0(X16,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_xboole_0(X2,X3)
           => r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t141_funct_1])).

cnf(c_0_12,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk3_0)
    & v1_funct_1(esk3_0)
    & r1_xboole_0(esk4_0,esk5_0)
    & ~ r1_xboole_0(k10_relat_1(esk3_0,esk4_0),k10_relat_1(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_15,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(X24,X25)
      | r1_tarski(k10_relat_1(X26,X24),k10_relat_1(X26,X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).

cnf(c_0_16,plain,
    ( k10_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_xboole_0(k2_tarski(X17,X18),X19)
      | ~ r2_hidden(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).

fof(c_0_19,plain,(
    ! [X10,X11,X13,X14,X15] :
      ( ( r1_xboole_0(X10,X11)
        | r2_hidden(esk2_2(X10,X11),k3_xboole_0(X10,X11)) )
      & ( ~ r2_hidden(X15,k3_xboole_0(X13,X14))
        | ~ r1_xboole_0(X13,X14) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_20,plain,(
    ! [X20,X21] : k1_setfam_1(k2_tarski(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_21,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_22,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( ~ r1_xboole_0(k2_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X27,X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ v1_funct_1(X29)
      | k10_relat_1(X29,k3_xboole_0(X27,X28)) = k3_xboole_0(k10_relat_1(X29,X27),k10_relat_1(X29,X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).

cnf(c_0_28,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17])])).

cnf(c_0_30,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_13])).

cnf(c_0_31,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( k10_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(X1,k10_relat_1(esk3_0,X2))
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_38,plain,
    ( k10_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))) = k1_setfam_1(k2_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_26]),c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_xboole_0(X1,X2)
    | ~ r2_hidden(X3,k10_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))
    | r2_hidden(esk2_2(k10_relat_1(X1,X2),k10_relat_1(X1,X3)),k10_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_xboole_0(k10_relat_1(esk3_0,esk4_0),k10_relat_1(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( r1_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_17])])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:20:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.19/0.37  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.19/0.37  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.37  fof(t141_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_xboole_0(X2,X3)=>r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_funct_1)).
% 0.19/0.37  fof(t178_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>r1_tarski(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 0.19/0.37  fof(t55_zfmisc_1, axiom, ![X1, X2, X3]:~((r1_xboole_0(k2_tarski(X1,X2),X3)&r2_hidden(X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 0.19/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.37  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.19/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.37  fof(t137_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>k10_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 0.19/0.37  fof(c_0_9, plain, ![X22, X23]:((k10_relat_1(X23,X22)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X23),X22)|~v1_relat_1(X23))&(~r1_xboole_0(k2_relat_1(X23),X22)|k10_relat_1(X23,X22)=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X16]:r1_xboole_0(X16,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.37  fof(c_0_11, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_xboole_0(X2,X3)=>r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))))), inference(assume_negation,[status(cth)],[t141_funct_1])).
% 0.19/0.37  cnf(c_0_12, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_13, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&(r1_xboole_0(esk4_0,esk5_0)&~r1_xboole_0(k10_relat_1(esk3_0,esk4_0),k10_relat_1(esk3_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.19/0.37  fof(c_0_15, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(X24,X25)|r1_tarski(k10_relat_1(X26,X24),k10_relat_1(X26,X25)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t178_relat_1])])).
% 0.19/0.37  cnf(c_0_16, plain, (k10_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_18, plain, ![X17, X18, X19]:(~r1_xboole_0(k2_tarski(X17,X18),X19)|~r2_hidden(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_zfmisc_1])])).
% 0.19/0.37  fof(c_0_19, plain, ![X10, X11, X13, X14, X15]:((r1_xboole_0(X10,X11)|r2_hidden(esk2_2(X10,X11),k3_xboole_0(X10,X11)))&(~r2_hidden(X15,k3_xboole_0(X13,X14))|~r1_xboole_0(X13,X14))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.37  fof(c_0_20, plain, ![X20, X21]:k1_setfam_1(k2_tarski(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.19/0.37  fof(c_0_21, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.37  cnf(c_0_22, plain, (r1_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k10_relat_1(esk3_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.37  cnf(c_0_24, plain, (~r1_xboole_0(k2_tarski(X1,X2),X3)|~r2_hidden(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_25, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  fof(c_0_27, plain, ![X27, X28, X29]:(~v1_relat_1(X29)|~v1_funct_1(X29)|k10_relat_1(X29,k3_xboole_0(X27,X28))=k3_xboole_0(k10_relat_1(X29,X27),k10_relat_1(X29,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t137_funct_1])])).
% 0.19/0.37  cnf(c_0_28, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_17])])).
% 0.19/0.37  cnf(c_0_30, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_13])).
% 0.19/0.37  cnf(c_0_31, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.37  cnf(c_0_32, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_33, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_34, plain, (k10_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_35, negated_conjecture, (~r2_hidden(X1,k10_relat_1(esk3_0,X2))|~r1_tarski(X2,k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.19/0.37  cnf(c_0_36, plain, (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X3)|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.37  cnf(c_0_37, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk2_2(X1,X2),k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_33, c_0_26])).
% 0.19/0.37  cnf(c_0_38, plain, (k10_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))=k1_setfam_1(k2_tarski(k10_relat_1(X1,X2),k10_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_26]), c_0_26])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (~r1_xboole_0(X1,X2)|~r2_hidden(X3,k10_relat_1(esk3_0,k1_setfam_1(k2_tarski(X1,X2))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.37  cnf(c_0_40, plain, (r1_xboole_0(k10_relat_1(X1,X2),k10_relat_1(X1,X3))|r2_hidden(esk2_2(k10_relat_1(X1,X2),k10_relat_1(X1,X3)),k10_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (~r1_xboole_0(k10_relat_1(esk3_0,esk4_0),k10_relat_1(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_43, negated_conjecture, (r1_xboole_0(k10_relat_1(esk3_0,X1),k10_relat_1(esk3_0,X2))|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_17])])).
% 0.19/0.37  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 46
% 0.19/0.37  # Proof object clause steps            : 27
% 0.19/0.37  # Proof object formula steps           : 19
% 0.19/0.37  # Proof object conjectures             : 13
% 0.19/0.37  # Proof object clause conjectures      : 10
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 14
% 0.19/0.37  # Proof object initial formulas used   : 9
% 0.19/0.37  # Proof object generating inferences   : 10
% 0.19/0.37  # Proof object simplifying inferences  : 12
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 9
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 16
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 15
% 0.19/0.37  # Processed clauses                    : 84
% 0.19/0.37  # ...of these trivial                  : 1
% 0.19/0.37  # ...subsumed                          : 21
% 0.19/0.37  # ...remaining for further processing  : 62
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 1
% 0.19/0.37  # Backward-rewritten                   : 0
% 0.19/0.37  # Generated clauses                    : 145
% 0.19/0.37  # ...of the previous two non-trivial   : 120
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 145
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 0
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 46
% 0.19/0.37  #    Positive orientable unit clauses  : 15
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 5
% 0.19/0.37  #    Non-unit-clauses                  : 26
% 0.19/0.37  # Current number of unprocessed clauses: 64
% 0.19/0.37  # ...number of literals in the above   : 140
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 17
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 57
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 39
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.19/0.37  # Unit Clause-clause subsumption calls : 16
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 11
% 0.19/0.37  # BW rewrite match successes           : 0
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3671
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.033 s
% 0.19/0.37  # System time              : 0.003 s
% 0.19/0.37  # Total time               : 0.035 s
% 0.19/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
