%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:29 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   40 (  87 expanded)
%              Number of clauses        :   21 (  34 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  107 ( 277 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,X2)
        & v1_finset_1(X2) )
     => v1_finset_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(fc14_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_finset_1)).

fof(t26_finset_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_finset_1(k1_relat_1(X1))
       => v1_finset_1(k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_finset_1)).

fof(t29_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_finset_1(k1_relat_1(X1))
      <=> v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_finset_1)).

fof(t100_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_funct_3)).

fof(redefinition_k9_funct_3,axiom,(
    ! [X1,X2] : k9_funct_3(X1,X2) = k7_funct_3(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_funct_3)).

fof(fc13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k9_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

fof(dt_k7_funct_3,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(k7_funct_3(X1,X2))
      & v1_funct_1(k7_funct_3(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_funct_3)).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ~ r1_tarski(X13,X14)
      | ~ v1_finset_1(X14)
      | v1_finset_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).

fof(c_0_10,plain,(
    ! [X3] :
      ( ~ v1_relat_1(X3)
      | r1_tarski(X3,k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_11,plain,
    ( v1_finset_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X8,X9] :
      ( ~ v1_finset_1(X8)
      | ~ v1_finset_1(X9)
      | v1_finset_1(k2_zfmisc_1(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).

cnf(c_0_14,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,plain,
    ( v1_finset_1(k2_zfmisc_1(X1,X2))
    | ~ v1_finset_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X15] :
      ( ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | ~ v1_finset_1(k1_relat_1(X15))
      | v1_finset_1(k2_relat_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_finset_1])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_finset_1(k1_relat_1(X1))
        <=> v1_finset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_finset_1])).

fof(c_0_18,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | k9_relat_1(k9_funct_3(k1_relat_1(X12),k2_relat_1(X12)),X12) = k1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).

fof(c_0_19,plain,(
    ! [X10,X11] : k9_funct_3(X10,X11) = k7_funct_3(X10,X11) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_funct_3])).

cnf(c_0_20,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_relat_1(X1))
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( v1_finset_1(k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_finset_1(k1_relat_1(esk1_0))
      | ~ v1_finset_1(esk1_0) )
    & ( v1_finset_1(k1_relat_1(esk1_0))
      | v1_finset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_23,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | ~ v1_finset_1(X7)
      | v1_finset_1(k9_relat_1(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).

cnf(c_0_24,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k9_funct_3(X1,X2) = k7_funct_3(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k7_funct_3(X4,X5))
      & v1_funct_1(k7_funct_3(X4,X5)) ) ),
    inference(variable_rename,[status(thm)],[dt_k7_funct_3])).

cnf(c_0_27,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk1_0))
    | v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_finset_1(k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k9_relat_1(k7_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,plain,
    ( v1_funct_1(k7_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(k7_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk1_0))
    | ~ v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v1_finset_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_37,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_36]),c_0_29])]),c_0_38]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.08/0.28  % Computer   : n013.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % WCLimit    : 600
% 0.08/0.28  % DateTime   : Tue Dec  1 15:46:54 EST 2020
% 0.13/0.28  % CPUTime    : 
% 0.13/0.28  # Version: 2.5pre002
% 0.13/0.29  # No SInE strategy applied
% 0.13/0.29  # Trying AutoSched0 for 299 seconds
% 0.13/0.30  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.30  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.30  #
% 0.13/0.30  # Preprocessing time       : 0.013 s
% 0.13/0.30  # Presaturation interreduction done
% 0.13/0.30  
% 0.13/0.30  # Proof found!
% 0.13/0.30  # SZS status Theorem
% 0.13/0.30  # SZS output start CNFRefutation
% 0.13/0.30  fof(t13_finset_1, axiom, ![X1, X2]:((r1_tarski(X1,X2)&v1_finset_1(X2))=>v1_finset_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 0.13/0.30  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.13/0.30  fof(fc14_finset_1, axiom, ![X1, X2]:((v1_finset_1(X1)&v1_finset_1(X2))=>v1_finset_1(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_finset_1)).
% 0.13/0.30  fof(t26_finset_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))=>v1_finset_1(k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_finset_1)).
% 0.13/0.30  fof(t29_finset_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))<=>v1_finset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_finset_1)).
% 0.13/0.30  fof(t100_funct_3, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_funct_3)).
% 0.13/0.30  fof(redefinition_k9_funct_3, axiom, ![X1, X2]:k9_funct_3(X1,X2)=k7_funct_3(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_funct_3)).
% 0.13/0.30  fof(fc13_finset_1, axiom, ![X1, X2]:(((v1_relat_1(X1)&v1_funct_1(X1))&v1_finset_1(X2))=>v1_finset_1(k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_finset_1)).
% 0.13/0.30  fof(dt_k7_funct_3, axiom, ![X1, X2]:(v1_relat_1(k7_funct_3(X1,X2))&v1_funct_1(k7_funct_3(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_funct_3)).
% 0.13/0.30  fof(c_0_9, plain, ![X13, X14]:(~r1_tarski(X13,X14)|~v1_finset_1(X14)|v1_finset_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_finset_1])])).
% 0.13/0.30  fof(c_0_10, plain, ![X3]:(~v1_relat_1(X3)|r1_tarski(X3,k2_zfmisc_1(k1_relat_1(X3),k2_relat_1(X3)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.13/0.30  cnf(c_0_11, plain, (v1_finset_1(X1)|~r1_tarski(X1,X2)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.30  cnf(c_0_12, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.30  fof(c_0_13, plain, ![X8, X9]:(~v1_finset_1(X8)|~v1_finset_1(X9)|v1_finset_1(k2_zfmisc_1(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).
% 0.13/0.30  cnf(c_0_14, plain, (v1_finset_1(X1)|~v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.13/0.30  cnf(c_0_15, plain, (v1_finset_1(k2_zfmisc_1(X1,X2))|~v1_finset_1(X1)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.30  fof(c_0_16, plain, ![X15]:(~v1_relat_1(X15)|~v1_funct_1(X15)|(~v1_finset_1(k1_relat_1(X15))|v1_finset_1(k2_relat_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_finset_1])])).
% 0.13/0.30  fof(c_0_17, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))<=>v1_finset_1(X1)))), inference(assume_negation,[status(cth)],[t29_finset_1])).
% 0.13/0.30  fof(c_0_18, plain, ![X12]:(~v1_relat_1(X12)|~v1_funct_1(X12)|k9_relat_1(k9_funct_3(k1_relat_1(X12),k2_relat_1(X12)),X12)=k1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).
% 0.13/0.30  fof(c_0_19, plain, ![X10, X11]:k9_funct_3(X10,X11)=k7_funct_3(X10,X11), inference(variable_rename,[status(thm)],[redefinition_k9_funct_3])).
% 0.13/0.30  cnf(c_0_20, plain, (v1_finset_1(X1)|~v1_finset_1(k2_relat_1(X1))|~v1_finset_1(k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.30  cnf(c_0_21, plain, (v1_finset_1(k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_finset_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.30  fof(c_0_22, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((~v1_finset_1(k1_relat_1(esk1_0))|~v1_finset_1(esk1_0))&(v1_finset_1(k1_relat_1(esk1_0))|v1_finset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.13/0.30  fof(c_0_23, plain, ![X6, X7]:(~v1_relat_1(X6)|~v1_funct_1(X6)|~v1_finset_1(X7)|v1_finset_1(k9_relat_1(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).
% 0.13/0.30  cnf(c_0_24, plain, (k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.30  cnf(c_0_25, plain, (k9_funct_3(X1,X2)=k7_funct_3(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.30  fof(c_0_26, plain, ![X4, X5]:(v1_relat_1(k7_funct_3(X4,X5))&v1_funct_1(k7_funct_3(X4,X5))), inference(variable_rename,[status(thm)],[dt_k7_funct_3])).
% 0.13/0.30  cnf(c_0_27, plain, (v1_finset_1(X1)|~v1_finset_1(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.30  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.30  cnf(c_0_29, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.30  cnf(c_0_30, negated_conjecture, (v1_finset_1(k1_relat_1(esk1_0))|v1_finset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.30  cnf(c_0_31, plain, (v1_finset_1(k9_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.30  cnf(c_0_32, plain, (k9_relat_1(k7_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.30  cnf(c_0_33, plain, (v1_funct_1(k7_funct_3(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.30  cnf(c_0_34, plain, (v1_relat_1(k7_funct_3(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.30  cnf(c_0_35, negated_conjecture, (~v1_finset_1(k1_relat_1(esk1_0))|~v1_finset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.30  cnf(c_0_36, negated_conjecture, (v1_finset_1(esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30])).
% 0.13/0.30  cnf(c_0_37, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.30  cnf(c_0_38, negated_conjecture, (~v1_finset_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.13/0.30  cnf(c_0_39, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_36]), c_0_29])]), c_0_38]), ['proof']).
% 0.13/0.30  # SZS output end CNFRefutation
% 0.13/0.30  # Proof object total steps             : 40
% 0.13/0.30  # Proof object clause steps            : 21
% 0.13/0.30  # Proof object formula steps           : 19
% 0.13/0.30  # Proof object conjectures             : 10
% 0.13/0.30  # Proof object clause conjectures      : 7
% 0.13/0.30  # Proof object formula conjectures     : 3
% 0.13/0.30  # Proof object initial clauses used    : 13
% 0.13/0.30  # Proof object initial formulas used   : 9
% 0.13/0.30  # Proof object generating inferences   : 6
% 0.13/0.30  # Proof object simplifying inferences  : 13
% 0.13/0.30  # Training examples: 0 positive, 0 negative
% 0.13/0.30  # Parsed axioms                        : 9
% 0.13/0.30  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.30  # Initial clauses                      : 13
% 0.13/0.30  # Removed in clause preprocessing      : 1
% 0.13/0.30  # Initial clauses in saturation        : 12
% 0.13/0.30  # Processed clauses                    : 31
% 0.13/0.30  # ...of these trivial                  : 0
% 0.13/0.30  # ...subsumed                          : 0
% 0.13/0.30  # ...remaining for further processing  : 30
% 0.13/0.30  # Other redundant clauses eliminated   : 0
% 0.13/0.30  # Clauses deleted for lack of memory   : 0
% 0.13/0.30  # Backward-subsumed                    : 0
% 0.13/0.30  # Backward-rewritten                   : 2
% 0.13/0.30  # Generated clauses                    : 9
% 0.13/0.30  # ...of the previous two non-trivial   : 9
% 0.13/0.30  # Contextual simplify-reflections      : 1
% 0.13/0.30  # Paramodulations                      : 9
% 0.13/0.30  # Factorizations                       : 0
% 0.13/0.30  # Equation resolutions                 : 0
% 0.13/0.30  # Propositional unsat checks           : 0
% 0.13/0.30  #    Propositional check models        : 0
% 0.13/0.30  #    Propositional check unsatisfiable : 0
% 0.13/0.30  #    Propositional clauses             : 0
% 0.13/0.30  #    Propositional clauses after purity: 0
% 0.13/0.30  #    Propositional unsat core size     : 0
% 0.13/0.30  #    Propositional preprocessing time  : 0.000
% 0.13/0.30  #    Propositional encoding time       : 0.000
% 0.13/0.30  #    Propositional solver time         : 0.000
% 0.13/0.30  #    Success case prop preproc time    : 0.000
% 0.13/0.30  #    Success case prop encoding time   : 0.000
% 0.13/0.30  #    Success case prop solver time     : 0.000
% 0.13/0.30  # Current number of processed clauses  : 16
% 0.13/0.30  #    Positive orientable unit clauses  : 5
% 0.13/0.30  #    Positive unorientable unit clauses: 0
% 0.13/0.30  #    Negative unit clauses             : 1
% 0.13/0.30  #    Non-unit-clauses                  : 10
% 0.13/0.30  # Current number of unprocessed clauses: 2
% 0.13/0.30  # ...number of literals in the above   : 4
% 0.13/0.30  # Current number of archived formulas  : 0
% 0.13/0.30  # Current number of archived clauses   : 15
% 0.13/0.30  # Clause-clause subsumption calls (NU) : 34
% 0.13/0.30  # Rec. Clause-clause subsumption calls : 22
% 0.13/0.30  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.30  # Unit Clause-clause subsumption calls : 0
% 0.13/0.30  # Rewrite failures with RHS unbound    : 0
% 0.13/0.30  # BW rewrite match attempts            : 1
% 0.13/0.30  # BW rewrite match successes           : 1
% 0.13/0.30  # Condensation attempts                : 0
% 0.13/0.30  # Condensation successes               : 0
% 0.13/0.30  # Termbank termtop insertions          : 1134
% 0.13/0.30  
% 0.13/0.30  # -------------------------------------------------
% 0.13/0.30  # User time                : 0.012 s
% 0.13/0.30  # System time              : 0.003 s
% 0.13/0.30  # Total time               : 0.015 s
% 0.13/0.30  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
