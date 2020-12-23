%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:29 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   41 (  93 expanded)
%              Number of clauses        :   22 (  36 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 278 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t100_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_funct_3)).

fof(redefinition_k9_funct_3,axiom,(
    ! [X1,X2] : k9_funct_3(X1,X2) = k7_funct_3(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

fof(fc10_finset_1,axiom,(
    ! [X1,X2] :
      ( v1_finset_1(X2)
     => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_finset_1)).

fof(t22_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(fc13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k9_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_finset_1)).

fof(dt_k7_funct_3,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(k7_funct_3(X1,X2))
      & v1_funct_1(k7_funct_3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_funct_3)).

fof(t29_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_finset_1(k1_relat_1(X1))
      <=> v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_finset_1)).

fof(fc14_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_finset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_9,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | k9_relat_1(k9_funct_3(k1_relat_1(X19),k2_relat_1(X19)),X19) = k1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).

fof(c_0_10,plain,(
    ! [X17,X18] : k9_funct_3(X17,X18) = k7_funct_3(X17,X18) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_funct_3])).

fof(c_0_11,plain,(
    ! [X11,X12] :
      ( ~ v1_finset_1(X12)
      | v1_finset_1(k3_xboole_0(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_finset_1])])).

fof(c_0_12,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k3_xboole_0(X6,k2_zfmisc_1(k1_relat_1(X6),k2_relat_1(X6))) = X6 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).

fof(c_0_13,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ v1_funct_1(X13)
      | ~ v1_finset_1(X14)
      | v1_finset_1(k9_relat_1(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).

cnf(c_0_14,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k9_funct_3(X1,X2) = k7_funct_3(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( v1_relat_1(k7_funct_3(X9,X10))
      & v1_funct_1(k7_funct_3(X9,X10)) ) ),
    inference(variable_rename,[status(thm)],[dt_k7_funct_3])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_finset_1(k1_relat_1(X1))
        <=> v1_finset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_finset_1])).

cnf(c_0_18,plain,
    ( v1_finset_1(k3_xboole_0(X2,X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X15,X16] :
      ( ~ v1_finset_1(X15)
      | ~ v1_finset_1(X16)
      | v1_finset_1(k2_zfmisc_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ~ v1_relat_1(X5)
      | k9_relat_1(X5,k1_relat_1(X5)) = k2_relat_1(X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_22,plain,
    ( v1_finset_1(k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k9_relat_1(k7_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,plain,
    ( v1_funct_1(k7_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_relat_1(k7_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_finset_1(k1_relat_1(esk1_0))
      | ~ v1_finset_1(esk1_0) )
    & ( v1_finset_1(k1_relat_1(esk1_0))
      | v1_finset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_27,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_28,plain,
    ( v1_finset_1(k2_zfmisc_1(X1,X2))
    | ~ v1_finset_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk1_0))
    | v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_relat_1(X1))
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( v1_finset_1(k2_relat_1(X1))
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk1_0))
    | ~ v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_38,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_finset_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_37])])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_37]),c_0_32])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:58:30 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.11/0.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.11/0.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.11/0.35  #
% 0.11/0.35  # Preprocessing time       : 0.027 s
% 0.11/0.35  # Presaturation interreduction done
% 0.11/0.35  
% 0.11/0.35  # Proof found!
% 0.11/0.35  # SZS status Theorem
% 0.11/0.35  # SZS output start CNFRefutation
% 0.11/0.35  fof(t100_funct_3, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_funct_3)).
% 0.11/0.35  fof(redefinition_k9_funct_3, axiom, ![X1, X2]:k9_funct_3(X1,X2)=k7_funct_3(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_funct_3)).
% 0.11/0.35  fof(fc10_finset_1, axiom, ![X1, X2]:(v1_finset_1(X2)=>v1_finset_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_finset_1)).
% 0.11/0.35  fof(t22_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 0.11/0.35  fof(fc13_finset_1, axiom, ![X1, X2]:(((v1_relat_1(X1)&v1_funct_1(X1))&v1_finset_1(X2))=>v1_finset_1(k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_finset_1)).
% 0.11/0.35  fof(dt_k7_funct_3, axiom, ![X1, X2]:(v1_relat_1(k7_funct_3(X1,X2))&v1_funct_1(k7_funct_3(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_funct_3)).
% 0.11/0.35  fof(t29_finset_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))<=>v1_finset_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_finset_1)).
% 0.11/0.35  fof(fc14_finset_1, axiom, ![X1, X2]:((v1_finset_1(X1)&v1_finset_1(X2))=>v1_finset_1(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_finset_1)).
% 0.11/0.35  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.11/0.35  fof(c_0_9, plain, ![X19]:(~v1_relat_1(X19)|~v1_funct_1(X19)|k9_relat_1(k9_funct_3(k1_relat_1(X19),k2_relat_1(X19)),X19)=k1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).
% 0.11/0.35  fof(c_0_10, plain, ![X17, X18]:k9_funct_3(X17,X18)=k7_funct_3(X17,X18), inference(variable_rename,[status(thm)],[redefinition_k9_funct_3])).
% 0.11/0.35  fof(c_0_11, plain, ![X11, X12]:(~v1_finset_1(X12)|v1_finset_1(k3_xboole_0(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_finset_1])])).
% 0.11/0.35  fof(c_0_12, plain, ![X6]:(~v1_relat_1(X6)|k3_xboole_0(X6,k2_zfmisc_1(k1_relat_1(X6),k2_relat_1(X6)))=X6), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).
% 0.11/0.35  fof(c_0_13, plain, ![X13, X14]:(~v1_relat_1(X13)|~v1_funct_1(X13)|~v1_finset_1(X14)|v1_finset_1(k9_relat_1(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).
% 0.11/0.35  cnf(c_0_14, plain, (k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.35  cnf(c_0_15, plain, (k9_funct_3(X1,X2)=k7_funct_3(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.11/0.35  fof(c_0_16, plain, ![X9, X10]:(v1_relat_1(k7_funct_3(X9,X10))&v1_funct_1(k7_funct_3(X9,X10))), inference(variable_rename,[status(thm)],[dt_k7_funct_3])).
% 0.11/0.35  fof(c_0_17, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))<=>v1_finset_1(X1)))), inference(assume_negation,[status(cth)],[t29_finset_1])).
% 0.11/0.35  cnf(c_0_18, plain, (v1_finset_1(k3_xboole_0(X2,X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.35  cnf(c_0_19, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.35  fof(c_0_20, plain, ![X15, X16]:(~v1_finset_1(X15)|~v1_finset_1(X16)|v1_finset_1(k2_zfmisc_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).
% 0.11/0.35  fof(c_0_21, plain, ![X5]:(~v1_relat_1(X5)|k9_relat_1(X5,k1_relat_1(X5))=k2_relat_1(X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.11/0.35  cnf(c_0_22, plain, (v1_finset_1(k9_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.11/0.35  cnf(c_0_23, plain, (k9_relat_1(k7_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.11/0.35  cnf(c_0_24, plain, (v1_funct_1(k7_funct_3(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.35  cnf(c_0_25, plain, (v1_relat_1(k7_funct_3(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.11/0.35  fof(c_0_26, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((~v1_finset_1(k1_relat_1(esk1_0))|~v1_finset_1(esk1_0))&(v1_finset_1(k1_relat_1(esk1_0))|v1_finset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.11/0.35  cnf(c_0_27, plain, (v1_finset_1(X1)|~v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.11/0.35  cnf(c_0_28, plain, (v1_finset_1(k2_zfmisc_1(X1,X2))|~v1_finset_1(X1)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.11/0.35  cnf(c_0_29, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.35  cnf(c_0_30, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.11/0.35  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.35  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.35  cnf(c_0_33, negated_conjecture, (v1_finset_1(k1_relat_1(esk1_0))|v1_finset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.35  cnf(c_0_34, plain, (v1_finset_1(X1)|~v1_finset_1(k2_relat_1(X1))|~v1_finset_1(k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.11/0.35  cnf(c_0_35, plain, (v1_finset_1(k2_relat_1(X1))|~v1_finset_1(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_29])).
% 0.11/0.35  cnf(c_0_36, negated_conjecture, (~v1_finset_1(k1_relat_1(esk1_0))|~v1_finset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.11/0.35  cnf(c_0_37, negated_conjecture, (v1_finset_1(k1_relat_1(esk1_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.11/0.35  cnf(c_0_38, plain, (v1_finset_1(X1)|~v1_finset_1(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.11/0.35  cnf(c_0_39, negated_conjecture, (~v1_finset_1(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_37])])).
% 0.11/0.35  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_37]), c_0_32])]), c_0_39]), ['proof']).
% 0.11/0.35  # SZS output end CNFRefutation
% 0.11/0.35  # Proof object total steps             : 41
% 0.11/0.35  # Proof object clause steps            : 22
% 0.11/0.35  # Proof object formula steps           : 19
% 0.11/0.35  # Proof object conjectures             : 10
% 0.11/0.35  # Proof object clause conjectures      : 7
% 0.11/0.35  # Proof object formula conjectures     : 3
% 0.11/0.35  # Proof object initial clauses used    : 13
% 0.11/0.35  # Proof object initial formulas used   : 9
% 0.11/0.35  # Proof object generating inferences   : 7
% 0.11/0.35  # Proof object simplifying inferences  : 13
% 0.11/0.35  # Training examples: 0 positive, 0 negative
% 0.11/0.35  # Parsed axioms                        : 12
% 0.11/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.35  # Initial clauses                      : 16
% 0.11/0.35  # Removed in clause preprocessing      : 1
% 0.11/0.35  # Initial clauses in saturation        : 15
% 0.11/0.35  # Processed clauses                    : 37
% 0.11/0.35  # ...of these trivial                  : 0
% 0.11/0.35  # ...subsumed                          : 0
% 0.11/0.35  # ...remaining for further processing  : 37
% 0.11/0.35  # Other redundant clauses eliminated   : 0
% 0.11/0.35  # Clauses deleted for lack of memory   : 0
% 0.11/0.35  # Backward-subsumed                    : 1
% 0.11/0.35  # Backward-rewritten                   : 1
% 0.11/0.35  # Generated clauses                    : 18
% 0.11/0.35  # ...of the previous two non-trivial   : 15
% 0.11/0.35  # Contextual simplify-reflections      : 1
% 0.11/0.35  # Paramodulations                      : 18
% 0.11/0.35  # Factorizations                       : 0
% 0.11/0.35  # Equation resolutions                 : 0
% 0.11/0.35  # Propositional unsat checks           : 0
% 0.11/0.35  #    Propositional check models        : 0
% 0.11/0.35  #    Propositional check unsatisfiable : 0
% 0.11/0.35  #    Propositional clauses             : 0
% 0.11/0.35  #    Propositional clauses after purity: 0
% 0.11/0.35  #    Propositional unsat core size     : 0
% 0.11/0.35  #    Propositional preprocessing time  : 0.000
% 0.11/0.35  #    Propositional encoding time       : 0.000
% 0.11/0.35  #    Propositional solver time         : 0.000
% 0.11/0.35  #    Success case prop preproc time    : 0.000
% 0.11/0.35  #    Success case prop encoding time   : 0.000
% 0.11/0.35  #    Success case prop solver time     : 0.000
% 0.11/0.35  # Current number of processed clauses  : 20
% 0.11/0.35  #    Positive orientable unit clauses  : 5
% 0.11/0.35  #    Positive unorientable unit clauses: 0
% 0.11/0.35  #    Negative unit clauses             : 1
% 0.11/0.35  #    Non-unit-clauses                  : 14
% 0.11/0.35  # Current number of unprocessed clauses: 8
% 0.11/0.35  # ...number of literals in the above   : 26
% 0.11/0.35  # Current number of archived formulas  : 0
% 0.11/0.35  # Current number of archived clauses   : 18
% 0.11/0.35  # Clause-clause subsumption calls (NU) : 22
% 0.11/0.35  # Rec. Clause-clause subsumption calls : 15
% 0.11/0.35  # Non-unit clause-clause subsumptions  : 1
% 0.11/0.35  # Unit Clause-clause subsumption calls : 1
% 0.11/0.35  # Rewrite failures with RHS unbound    : 0
% 0.11/0.35  # BW rewrite match attempts            : 1
% 0.11/0.35  # BW rewrite match successes           : 1
% 0.11/0.35  # Condensation attempts                : 0
% 0.11/0.35  # Condensation successes               : 0
% 0.11/0.35  # Termbank termtop insertions          : 1420
% 0.11/0.35  
% 0.11/0.35  # -------------------------------------------------
% 0.11/0.35  # User time                : 0.031 s
% 0.11/0.35  # System time              : 0.001 s
% 0.11/0.35  # Total time               : 0.032 s
% 0.11/0.35  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
