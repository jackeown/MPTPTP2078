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

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  90 expanded)
%              Number of clauses        :   22 (  35 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  113 ( 282 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc10_finset_1,axiom,(
    ! [X1,X2] :
      ( v1_finset_1(X2)
     => v1_finset_1(k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_finset_1)).

fof(t22_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(dt_k9_funct_3,axiom,(
    ! [X1,X2] :
      ( v1_funct_1(k9_funct_3(X1,X2))
      & v1_funct_2(k9_funct_3(X1,X2),k2_zfmisc_1(X1,X2),X1)
      & m1_subset_1(k9_funct_3(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_funct_3)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(fc13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k9_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_finset_1)).

fof(t100_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_funct_3)).

fof(c_0_10,plain,(
    ! [X10,X11] :
      ( ~ v1_finset_1(X11)
      | v1_finset_1(k3_xboole_0(X10,X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_finset_1])])).

fof(c_0_11,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | k3_xboole_0(X7,k2_zfmisc_1(k1_relat_1(X7),k2_relat_1(X7))) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).

cnf(c_0_12,plain,
    ( v1_finset_1(k3_xboole_0(X2,X1))
    | ~ v1_finset_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ~ v1_finset_1(X14)
      | ~ v1_finset_1(X15)
      | v1_finset_1(k2_zfmisc_1(X14,X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).

cnf(c_0_15,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_16,plain,
    ( v1_finset_1(k2_zfmisc_1(X1,X2))
    | ~ v1_finset_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_17,plain,(
    ! [X17] :
      ( ~ v1_relat_1(X17)
      | ~ v1_funct_1(X17)
      | ~ v1_finset_1(k1_relat_1(X17))
      | v1_finset_1(k2_relat_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_finset_1])])).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_finset_1(k1_relat_1(X1))
        <=> v1_finset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_finset_1])).

fof(c_0_19,plain,(
    ! [X3,X4] :
      ( ~ v1_relat_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_relat_1(X4) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k9_funct_3(X8,X9))
      & v1_funct_2(k9_funct_3(X8,X9),k2_zfmisc_1(X8,X9),X8)
      & m1_subset_1(k9_funct_3(X8,X9),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X8))) ) ),
    inference(variable_rename,[status(thm)],[dt_k9_funct_3])).

fof(c_0_21,plain,(
    ! [X5,X6] : v1_relat_1(k2_zfmisc_1(X5,X6)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_22,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_relat_1(X1))
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( v1_finset_1(k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_finset_1(k1_relat_1(esk1_0))
      | ~ v1_finset_1(esk1_0) )
    & ( v1_finset_1(k1_relat_1(esk1_0))
      | v1_finset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_25,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X12)
      | ~ v1_funct_1(X12)
      | ~ v1_finset_1(X13)
      | v1_finset_1(k9_relat_1(X12,X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).

fof(c_0_26,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | ~ v1_funct_1(X16)
      | k9_relat_1(k9_funct_3(k1_relat_1(X16),k2_relat_1(X16)),X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).

cnf(c_0_27,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( m1_subset_1(k9_funct_3(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk1_0))
    | v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( v1_finset_1(k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( v1_funct_1(k9_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( v1_relat_1(k9_funct_3(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk1_0))
    | ~ v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( v1_finset_1(esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])]),c_0_33])).

cnf(c_0_40,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),c_0_37])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_31]),c_0_39]),c_0_32])]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:34:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.027 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(fc10_finset_1, axiom, ![X1, X2]:(v1_finset_1(X2)=>v1_finset_1(k3_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_finset_1)).
% 0.19/0.37  fof(t22_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 0.19/0.37  fof(fc14_finset_1, axiom, ![X1, X2]:((v1_finset_1(X1)&v1_finset_1(X2))=>v1_finset_1(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_finset_1)).
% 0.19/0.37  fof(t26_finset_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))=>v1_finset_1(k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_finset_1)).
% 0.19/0.37  fof(t29_finset_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))<=>v1_finset_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_finset_1)).
% 0.19/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.37  fof(dt_k9_funct_3, axiom, ![X1, X2]:((v1_funct_1(k9_funct_3(X1,X2))&v1_funct_2(k9_funct_3(X1,X2),k2_zfmisc_1(X1,X2),X1))&m1_subset_1(k9_funct_3(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_funct_3)).
% 0.19/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.37  fof(fc13_finset_1, axiom, ![X1, X2]:(((v1_relat_1(X1)&v1_funct_1(X1))&v1_finset_1(X2))=>v1_finset_1(k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_finset_1)).
% 0.19/0.37  fof(t100_funct_3, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_funct_3)).
% 0.19/0.37  fof(c_0_10, plain, ![X10, X11]:(~v1_finset_1(X11)|v1_finset_1(k3_xboole_0(X10,X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc10_finset_1])])).
% 0.19/0.37  fof(c_0_11, plain, ![X7]:(~v1_relat_1(X7)|k3_xboole_0(X7,k2_zfmisc_1(k1_relat_1(X7),k2_relat_1(X7)))=X7), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t22_relat_1])])).
% 0.19/0.37  cnf(c_0_12, plain, (v1_finset_1(k3_xboole_0(X2,X1))|~v1_finset_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_13, plain, (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.37  fof(c_0_14, plain, ![X14, X15]:(~v1_finset_1(X14)|~v1_finset_1(X15)|v1_finset_1(k2_zfmisc_1(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).
% 0.19/0.37  cnf(c_0_15, plain, (v1_finset_1(X1)|~v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.37  cnf(c_0_16, plain, (v1_finset_1(k2_zfmisc_1(X1,X2))|~v1_finset_1(X1)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  fof(c_0_17, plain, ![X17]:(~v1_relat_1(X17)|~v1_funct_1(X17)|(~v1_finset_1(k1_relat_1(X17))|v1_finset_1(k2_relat_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_finset_1])])).
% 0.19/0.37  fof(c_0_18, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_finset_1(k1_relat_1(X1))<=>v1_finset_1(X1)))), inference(assume_negation,[status(cth)],[t29_finset_1])).
% 0.19/0.37  fof(c_0_19, plain, ![X3, X4]:(~v1_relat_1(X3)|(~m1_subset_1(X4,k1_zfmisc_1(X3))|v1_relat_1(X4))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.37  fof(c_0_20, plain, ![X8, X9]:((v1_funct_1(k9_funct_3(X8,X9))&v1_funct_2(k9_funct_3(X8,X9),k2_zfmisc_1(X8,X9),X8))&m1_subset_1(k9_funct_3(X8,X9),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X8,X9),X8)))), inference(variable_rename,[status(thm)],[dt_k9_funct_3])).
% 0.19/0.37  fof(c_0_21, plain, ![X5, X6]:v1_relat_1(k2_zfmisc_1(X5,X6)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.37  cnf(c_0_22, plain, (v1_finset_1(X1)|~v1_finset_1(k2_relat_1(X1))|~v1_finset_1(k1_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.37  cnf(c_0_23, plain, (v1_finset_1(k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_finset_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  fof(c_0_24, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&((~v1_finset_1(k1_relat_1(esk1_0))|~v1_finset_1(esk1_0))&(v1_finset_1(k1_relat_1(esk1_0))|v1_finset_1(esk1_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.19/0.37  fof(c_0_25, plain, ![X12, X13]:(~v1_relat_1(X12)|~v1_funct_1(X12)|~v1_finset_1(X13)|v1_finset_1(k9_relat_1(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).
% 0.19/0.37  fof(c_0_26, plain, ![X16]:(~v1_relat_1(X16)|~v1_funct_1(X16)|k9_relat_1(k9_funct_3(k1_relat_1(X16),k2_relat_1(X16)),X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).
% 0.19/0.37  cnf(c_0_27, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_28, plain, (m1_subset_1(k9_funct_3(X1,X2),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X1)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_29, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_30, plain, (v1_finset_1(X1)|~v1_finset_1(k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_33, negated_conjecture, (v1_finset_1(k1_relat_1(esk1_0))|v1_finset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_34, plain, (v1_finset_1(k9_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_finset_1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_35, plain, (k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_36, plain, (v1_funct_1(k9_funct_3(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.37  cnf(c_0_37, plain, (v1_relat_1(k9_funct_3(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])])).
% 0.19/0.37  cnf(c_0_38, negated_conjecture, (~v1_finset_1(k1_relat_1(esk1_0))|~v1_finset_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.37  cnf(c_0_39, negated_conjecture, (v1_finset_1(esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])]), c_0_33])).
% 0.19/0.37  cnf(c_0_40, plain, (v1_finset_1(k1_relat_1(X1))|~v1_finset_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), c_0_37])])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (~v1_finset_1(k1_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_31]), c_0_39]), c_0_32])]), c_0_41]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 43
% 0.19/0.37  # Proof object clause steps            : 22
% 0.19/0.37  # Proof object formula steps           : 21
% 0.19/0.37  # Proof object conjectures             : 10
% 0.19/0.37  # Proof object clause conjectures      : 7
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 14
% 0.19/0.37  # Proof object initial formulas used   : 10
% 0.19/0.37  # Proof object generating inferences   : 7
% 0.19/0.37  # Proof object simplifying inferences  : 15
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 10
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 15
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 15
% 0.19/0.37  # Processed clauses                    : 38
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 38
% 0.19/0.37  # Other redundant clauses eliminated   : 0
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 2
% 0.19/0.37  # Generated clauses                    : 10
% 0.19/0.37  # ...of the previous two non-trivial   : 8
% 0.19/0.37  # Contextual simplify-reflections      : 1
% 0.19/0.37  # Paramodulations                      : 10
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
% 0.19/0.37  # Current number of processed clauses  : 21
% 0.19/0.37  #    Positive orientable unit clauses  : 8
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 12
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 17
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 17
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 6
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 0
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 1
% 0.19/0.37  # BW rewrite match successes           : 1
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1327
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.028 s
% 0.19/0.37  # System time              : 0.004 s
% 0.19/0.37  # Total time               : 0.032 s
% 0.19/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
