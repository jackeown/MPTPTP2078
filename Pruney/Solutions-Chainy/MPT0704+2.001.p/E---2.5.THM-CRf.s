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
% DateTime   : Thu Dec  3 10:55:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 320 expanded)
%              Number of clauses        :   33 ( 131 expanded)
%              Number of leaves         :    6 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  146 (1190 expanded)
%              Number of equality atoms :   31 ( 181 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2] :
          ? [X3] : r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k1_tarski(X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t144_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ! [X2] :
            ~ ( r2_hidden(X2,k2_relat_1(X1))
              & ! [X3] : k10_relat_1(X1,k1_tarski(X2)) != k1_tarski(X3) )
      <=> v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t39_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2] :
            ? [X3] : r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k1_tarski(X3)) ) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_1])).

fof(c_0_7,plain,(
    ! [X19,X20] :
      ( ( ~ r2_hidden(X19,k2_relat_1(X20))
        | k10_relat_1(X20,k1_tarski(X19)) != k1_xboole_0
        | ~ v1_relat_1(X20) )
      & ( k10_relat_1(X20,k1_tarski(X19)) = k1_xboole_0
        | r2_hidden(X19,k2_relat_1(X20))
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_8,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_9,plain,(
    ! [X21,X23,X24] :
      ( ( r2_hidden(esk1_1(X21),k2_relat_1(X21))
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( k10_relat_1(X21,k1_tarski(esk1_1(X21))) != k1_tarski(X23)
        | v2_funct_1(X21)
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( ~ v2_funct_1(X21)
        | ~ r2_hidden(X24,k2_relat_1(X21))
        | k10_relat_1(X21,k1_tarski(X24)) = k1_tarski(esk2_2(X21,X24))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_funct_1])])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X28,X29] :
      ( v1_relat_1(esk3_0)
      & v1_funct_1(esk3_0)
      & ( ~ v2_funct_1(esk3_0)
        | ~ r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k1_tarski(X28)) )
      & ( v2_funct_1(esk3_0)
        | r1_tarski(k10_relat_1(esk3_0,k1_tarski(X29)),k1_tarski(esk5_1(X29))) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),k2_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_funct_1(esk3_0)
    | ~ r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_xboole_0
    | r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( k10_relat_1(X1,X2) != k1_xboole_0
    | ~ r2_hidden(X3,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_tarski(X3))
    | ~ r1_tarski(k1_tarski(X3),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | r2_hidden(esk1_1(esk3_0),k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_23,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1)))
    | ~ r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k10_relat_1(X1,k1_tarski(X2)) = k1_tarski(esk2_2(X1,X2))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_funct_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k1_tarski(esk4_0)),k1_tarski(X2))
    | ~ r1_tarski(esk3_0,X1)
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_27,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | k10_relat_1(esk3_0,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k1_tarski(esk1_1(esk3_0)))
    | ~ r1_tarski(k1_tarski(esk1_1(esk3_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1)))
    | ~ v2_funct_1(X2)
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,k2_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k10_relat_1(X2,k1_tarski(X3))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,k2_relat_1(esk3_0))
    | ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])).

cnf(c_0_32,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_28])])).

cnf(c_0_33,plain,
    ( v2_funct_1(X1)
    | k10_relat_1(X1,k1_tarski(esk1_1(X1))) != k1_tarski(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_14]),c_0_15])]),c_0_31]),c_0_17])).

fof(c_0_35,plain,(
    ! [X17,X18] :
      ( ( ~ r1_tarski(X17,k1_tarski(X18))
        | X17 = k1_xboole_0
        | X17 = k1_tarski(X18) )
      & ( X17 != k1_xboole_0
        | r1_tarski(X17,k1_tarski(X18)) )
      & ( X17 != k1_tarski(X18)
        | r1_tarski(X17,k1_tarski(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk3_0)
    | ~ r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_12])]),c_0_27])])).

cnf(c_0_37,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k1_tarski(esk1_1(X1))),k1_tarski(X2))
    | ~ r1_tarski(k1_tarski(X2),k10_relat_1(X1,k1_tarski(esk1_1(X1)))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_12])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_34]),c_0_28])])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( v2_funct_1(X1)
    | ~ r1_tarski(k10_relat_1(X1,k1_tarski(esk1_1(X1))),k1_xboole_0)
    | ~ r1_tarski(X1,esk3_0)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k1_tarski(esk5_1(esk1_1(esk3_0))),k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_14]),c_0_15])]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( k1_tarski(esk5_1(X1)) = k10_relat_1(esk3_0,k1_tarski(X1))
    | k10_relat_1(esk3_0,k1_tarski(X1)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_40]),c_0_28])])).

cnf(c_0_44,negated_conjecture,
    ( k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_27])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:58:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S059A
% 0.21/0.50  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.21/0.50  #
% 0.21/0.50  # Preprocessing time       : 0.027 s
% 0.21/0.50  # Presaturation interreduction done
% 0.21/0.50  
% 0.21/0.50  # Proof found!
% 0.21/0.50  # SZS status Theorem
% 0.21/0.50  # SZS output start CNFRefutation
% 0.21/0.50  fof(t159_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2]:?[X3]:r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k1_tarski(X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_funct_1)).
% 0.21/0.50  fof(t142_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 0.21/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.50  fof(t144_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(![X2]:~((r2_hidden(X2,k2_relat_1(X1))&![X3]:k10_relat_1(X1,k1_tarski(X2))!=k1_tarski(X3)))<=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_funct_1)).
% 0.21/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.50  fof(t39_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 0.21/0.50  fof(c_0_6, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2]:?[X3]:r1_tarski(k10_relat_1(X1,k1_tarski(X2)),k1_tarski(X3))))), inference(assume_negation,[status(cth)],[t159_funct_1])).
% 0.21/0.50  fof(c_0_7, plain, ![X19, X20]:((~r2_hidden(X19,k2_relat_1(X20))|k10_relat_1(X20,k1_tarski(X19))!=k1_xboole_0|~v1_relat_1(X20))&(k10_relat_1(X20,k1_tarski(X19))=k1_xboole_0|r2_hidden(X19,k2_relat_1(X20))|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).
% 0.21/0.50  fof(c_0_8, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.50  fof(c_0_9, plain, ![X21, X23, X24]:(((r2_hidden(esk1_1(X21),k2_relat_1(X21))|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(k10_relat_1(X21,k1_tarski(esk1_1(X21)))!=k1_tarski(X23)|v2_funct_1(X21)|(~v1_relat_1(X21)|~v1_funct_1(X21))))&(~v2_funct_1(X21)|(~r2_hidden(X24,k2_relat_1(X21))|k10_relat_1(X21,k1_tarski(X24))=k1_tarski(esk2_2(X21,X24)))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_funct_1])])])])])).
% 0.21/0.50  fof(c_0_10, negated_conjecture, ![X28, X29]:((v1_relat_1(esk3_0)&v1_funct_1(esk3_0))&((~v2_funct_1(esk3_0)|~r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k1_tarski(X28)))&(v2_funct_1(esk3_0)|r1_tarski(k10_relat_1(esk3_0,k1_tarski(X29)),k1_tarski(esk5_1(X29)))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.21/0.50  cnf(c_0_11, plain, (~r2_hidden(X1,k2_relat_1(X2))|k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.50  cnf(c_0_12, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.50  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),k2_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_16, negated_conjecture, (~v2_funct_1(esk3_0)|~r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_17, negated_conjecture, (v2_funct_1(esk3_0)|r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.50  cnf(c_0_18, plain, (k10_relat_1(X1,k1_tarski(X2))=k1_xboole_0|r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.50  fof(c_0_19, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.50  cnf(c_0_20, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.50  cnf(c_0_21, plain, (k10_relat_1(X1,X2)!=k1_xboole_0|~r2_hidden(X3,k2_relat_1(X1))|~v1_relat_1(X1)|~r1_tarski(X2,k1_tarski(X3))|~r1_tarski(k1_tarski(X3),X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.21/0.50  cnf(c_0_22, negated_conjecture, (v2_funct_1(esk3_0)|r2_hidden(esk1_1(esk3_0),k2_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.21/0.50  cnf(c_0_23, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1)))|~r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k1_tarski(X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.50  cnf(c_0_24, plain, (k10_relat_1(X1,k1_tarski(X2))=k1_tarski(esk2_2(X1,X2))|~v2_funct_1(X1)|~r2_hidden(X2,k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  cnf(c_0_25, negated_conjecture, (~v2_funct_1(X1)|~r1_tarski(k10_relat_1(X1,k1_tarski(esk4_0)),k1_tarski(X2))|~r1_tarski(esk3_0,X1)|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_12])).
% 0.21/0.50  cnf(c_0_26, negated_conjecture, (k10_relat_1(esk3_0,k1_tarski(X1))=k1_xboole_0|r2_hidden(X1,k2_relat_1(esk3_0))), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.21/0.50  cnf(c_0_27, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.50  cnf(c_0_28, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.50  cnf(c_0_29, negated_conjecture, (v2_funct_1(esk3_0)|k10_relat_1(esk3_0,X1)!=k1_xboole_0|~r1_tarski(X1,k1_tarski(esk1_1(esk3_0)))|~r1_tarski(k1_tarski(esk1_1(esk3_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_15])])).
% 0.21/0.50  cnf(c_0_30, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1)))|~v2_funct_1(X2)|~v1_funct_1(X2)|~r2_hidden(X3,k2_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk4_0)),k10_relat_1(X2,k1_tarski(X3)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.50  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,k2_relat_1(esk3_0))|~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])).
% 0.21/0.50  cnf(c_0_32, negated_conjecture, (v2_funct_1(esk3_0)|k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_28])])).
% 0.21/0.50  cnf(c_0_33, plain, (v2_funct_1(X1)|k10_relat_1(X1,k1_tarski(esk1_1(X1)))!=k1_tarski(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.50  cnf(c_0_34, negated_conjecture, (r1_tarski(k10_relat_1(esk3_0,k1_tarski(X1)),k1_tarski(esk5_1(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_28]), c_0_14]), c_0_15])]), c_0_31]), c_0_17])).
% 0.21/0.50  fof(c_0_35, plain, ![X17, X18]:((~r1_tarski(X17,k1_tarski(X18))|(X17=k1_xboole_0|X17=k1_tarski(X18)))&((X17!=k1_xboole_0|r1_tarski(X17,k1_tarski(X18)))&(X17!=k1_tarski(X18)|r1_tarski(X17,k1_tarski(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_zfmisc_1])])])).
% 0.21/0.50  cnf(c_0_36, negated_conjecture, (v2_funct_1(esk3_0)|~r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_12])]), c_0_27])])).
% 0.21/0.50  cnf(c_0_37, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k10_relat_1(X1,k1_tarski(esk1_1(X1))),k1_tarski(X2))|~r1_tarski(k1_tarski(X2),k10_relat_1(X1,k1_tarski(esk1_1(X1))))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_12])])).
% 0.21/0.50  cnf(c_0_38, negated_conjecture, (~v2_funct_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_34]), c_0_28])])).
% 0.21/0.50  cnf(c_0_39, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.50  cnf(c_0_40, negated_conjecture, (v2_funct_1(X1)|~r1_tarski(k10_relat_1(X1,k1_tarski(esk1_1(X1))),k1_xboole_0)|~r1_tarski(X1,esk3_0)|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_12])).
% 0.21/0.50  cnf(c_0_41, negated_conjecture, (~r1_tarski(k1_tarski(esk5_1(esk1_1(esk3_0))),k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_14]), c_0_15])]), c_0_38])).
% 0.21/0.50  cnf(c_0_42, negated_conjecture, (k1_tarski(esk5_1(X1))=k10_relat_1(esk3_0,k1_tarski(X1))|k10_relat_1(esk3_0,k1_tarski(X1))=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_34])).
% 0.21/0.50  cnf(c_0_43, negated_conjecture, (~r1_tarski(k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_40]), c_0_28])])).
% 0.21/0.50  cnf(c_0_44, negated_conjecture, (k10_relat_1(esk3_0,k1_tarski(esk1_1(esk3_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_28])])).
% 0.21/0.50  cnf(c_0_45, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_27])]), ['proof']).
% 0.21/0.50  # SZS output end CNFRefutation
% 0.21/0.50  # Proof object total steps             : 46
% 0.21/0.50  # Proof object clause steps            : 33
% 0.21/0.50  # Proof object formula steps           : 13
% 0.21/0.50  # Proof object conjectures             : 24
% 0.21/0.50  # Proof object clause conjectures      : 21
% 0.21/0.50  # Proof object formula conjectures     : 3
% 0.21/0.50  # Proof object initial clauses used    : 13
% 0.21/0.50  # Proof object initial formulas used   : 6
% 0.21/0.50  # Proof object generating inferences   : 18
% 0.21/0.50  # Proof object simplifying inferences  : 32
% 0.21/0.50  # Training examples: 0 positive, 0 negative
% 0.21/0.50  # Parsed axioms                        : 9
% 0.21/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.50  # Initial clauses                      : 19
% 0.21/0.50  # Removed in clause preprocessing      : 0
% 0.21/0.50  # Initial clauses in saturation        : 19
% 0.21/0.50  # Processed clauses                    : 870
% 0.21/0.50  # ...of these trivial                  : 6
% 0.21/0.50  # ...subsumed                          : 479
% 0.21/0.50  # ...remaining for further processing  : 385
% 0.21/0.50  # Other redundant clauses eliminated   : 81
% 0.21/0.50  # Clauses deleted for lack of memory   : 0
% 0.21/0.50  # Backward-subsumed                    : 62
% 0.21/0.50  # Backward-rewritten                   : 75
% 0.21/0.50  # Generated clauses                    : 4629
% 0.21/0.50  # ...of the previous two non-trivial   : 4393
% 0.21/0.50  # Contextual simplify-reflections      : 13
% 0.21/0.50  # Paramodulations                      : 4545
% 0.21/0.50  # Factorizations                       : 2
% 0.21/0.50  # Equation resolutions                 : 81
% 0.21/0.50  # Propositional unsat checks           : 0
% 0.21/0.50  #    Propositional check models        : 0
% 0.21/0.50  #    Propositional check unsatisfiable : 0
% 0.21/0.50  #    Propositional clauses             : 0
% 0.21/0.50  #    Propositional clauses after purity: 0
% 0.21/0.50  #    Propositional unsat core size     : 0
% 0.21/0.50  #    Propositional preprocessing time  : 0.000
% 0.21/0.50  #    Propositional encoding time       : 0.000
% 0.21/0.50  #    Propositional solver time         : 0.000
% 0.21/0.50  #    Success case prop preproc time    : 0.000
% 0.21/0.50  #    Success case prop encoding time   : 0.000
% 0.21/0.50  #    Success case prop solver time     : 0.000
% 0.21/0.50  # Current number of processed clauses  : 227
% 0.21/0.50  #    Positive orientable unit clauses  : 10
% 0.21/0.50  #    Positive unorientable unit clauses: 0
% 0.21/0.50  #    Negative unit clauses             : 1
% 0.21/0.50  #    Non-unit-clauses                  : 216
% 0.21/0.50  # Current number of unprocessed clauses: 3503
% 0.21/0.50  # ...number of literals in the above   : 20181
% 0.21/0.50  # Current number of archived formulas  : 0
% 0.21/0.50  # Current number of archived clauses   : 154
% 0.21/0.50  # Clause-clause subsumption calls (NU) : 28987
% 0.21/0.50  # Rec. Clause-clause subsumption calls : 5445
% 0.21/0.50  # Non-unit clause-clause subsumptions  : 537
% 0.21/0.50  # Unit Clause-clause subsumption calls : 552
% 0.21/0.50  # Rewrite failures with RHS unbound    : 0
% 0.21/0.50  # BW rewrite match attempts            : 17
% 0.21/0.50  # BW rewrite match successes           : 6
% 0.21/0.50  # Condensation attempts                : 0
% 0.21/0.50  # Condensation successes               : 0
% 0.21/0.50  # Termbank termtop insertions          : 91804
% 0.21/0.50  
% 0.21/0.50  # -------------------------------------------------
% 0.21/0.50  # User time                : 0.143 s
% 0.21/0.50  # System time              : 0.010 s
% 0.21/0.50  # Total time               : 0.154 s
% 0.21/0.50  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
