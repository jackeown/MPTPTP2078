%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:53 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  69 expanded)
%              Number of clauses        :   19 (  24 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 384 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t83_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X1,X1,X2) = X1 )
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_funct_2)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc3_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) )
       => ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_2)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( ( v2_funct_1(X2)
            & k2_relset_1(X1,X1,X2) = X1 )
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,X1,X1)
            & v3_funct_2(X2,X1,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t83_funct_2])).

fof(c_0_8,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & v2_funct_1(esk2_0)
    & k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,esk1_0,esk1_0)
      | ~ v3_funct_2(esk2_0,esk1_0,esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X17,X18] :
      ( ( ~ v2_funct_2(X18,X17)
        | k2_relat_1(X18) = X17
        | ~ v1_relat_1(X18)
        | ~ v5_relat_1(X18,X17) )
      & ( k2_relat_1(X18) != X17
        | v2_funct_2(X18,X17)
        | ~ v1_relat_1(X18)
        | ~ v5_relat_1(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | k2_relset_1(X11,X12,X13) = k2_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_11,plain,(
    ! [X8,X9,X10] :
      ( ( v4_relat_1(X10,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( v5_relat_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_12,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | v1_relat_1(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,plain,(
    ! [X6,X7] : v1_relat_1(k2_zfmisc_1(X6,X7)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_14,plain,(
    ! [X14,X15,X16] :
      ( ( v1_funct_1(X16)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X16)
        | ~ v2_funct_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v3_funct_2(X16,X14,X15)
        | ~ v1_funct_1(X16)
        | ~ v2_funct_1(X16)
        | ~ v2_funct_2(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_2])])])).

cnf(c_0_15,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,esk1_0,esk1_0)
    | ~ v3_funct_2(esk2_0,esk1_0,esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v2_funct_2(X1,X2)
    | k2_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(esk1_0,esk1_0,esk2_0) = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( v3_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v2_funct_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( ~ v3_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_28,plain,
    ( v2_funct_2(X1,k2_relat_1(X1))
    | ~ v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(esk2_0) = esk1_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v5_relat_1(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_18])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_funct_2(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_26]),c_0_16])]),c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S011N
% 0.21/0.38  # and selection function PSelectDiffNegLit.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.027 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t83_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((v2_funct_1(X2)&k2_relset_1(X1,X1,X2)=X1)=>(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_funct_2)).
% 0.21/0.38  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 0.21/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.38  fof(cc3_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2))=>(v1_funct_1(X3)&v3_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_2)).
% 0.21/0.38  fof(c_0_7, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>((v2_funct_1(X2)&k2_relset_1(X1,X1,X2)=X1)=>(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))))), inference(assume_negation,[status(cth)],[t83_funct_2])).
% 0.21/0.38  fof(c_0_8, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&((v2_funct_1(esk2_0)&k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0)&(~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,esk1_0,esk1_0)|~v3_funct_2(esk2_0,esk1_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.21/0.38  fof(c_0_9, plain, ![X17, X18]:((~v2_funct_2(X18,X17)|k2_relat_1(X18)=X17|(~v1_relat_1(X18)|~v5_relat_1(X18,X17)))&(k2_relat_1(X18)!=X17|v2_funct_2(X18,X17)|(~v1_relat_1(X18)|~v5_relat_1(X18,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 0.21/0.38  fof(c_0_10, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|k2_relset_1(X11,X12,X13)=k2_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.38  fof(c_0_11, plain, ![X8, X9, X10]:((v4_relat_1(X10,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))))&(v5_relat_1(X10,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.38  fof(c_0_12, plain, ![X4, X5]:(~v1_relat_1(X4)|(~m1_subset_1(X5,k1_zfmisc_1(X4))|v1_relat_1(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.38  fof(c_0_13, plain, ![X6, X7]:v1_relat_1(k2_zfmisc_1(X6,X7)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.38  fof(c_0_14, plain, ![X14, X15, X16]:((v1_funct_1(X16)|(~v1_funct_1(X16)|~v2_funct_1(X16)|~v2_funct_2(X16,X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))&(v3_funct_2(X16,X14,X15)|(~v1_funct_1(X16)|~v2_funct_1(X16)|~v2_funct_2(X16,X15))|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_2])])])).
% 0.21/0.38  cnf(c_0_15, negated_conjecture, (~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,esk1_0,esk1_0)|~v3_funct_2(esk2_0,esk1_0,esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_19, plain, (v2_funct_2(X1,X2)|k2_relat_1(X1)!=X2|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.38  cnf(c_0_20, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.38  cnf(c_0_21, negated_conjecture, (k2_relset_1(esk1_0,esk1_0,esk2_0)=esk1_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_22, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.38  cnf(c_0_23, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.38  cnf(c_0_24, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.38  cnf(c_0_25, plain, (v3_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v2_funct_1(X1)|~v2_funct_2(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.38  cnf(c_0_26, negated_conjecture, (v2_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.38  cnf(c_0_27, negated_conjecture, (~v3_funct_2(esk2_0,esk1_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])).
% 0.21/0.38  cnf(c_0_28, plain, (v2_funct_2(X1,k2_relat_1(X1))|~v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_29, negated_conjecture, (k2_relat_1(esk2_0)=esk1_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_21])).
% 0.21/0.38  cnf(c_0_30, negated_conjecture, (v5_relat_1(esk2_0,esk1_0)), inference(spm,[status(thm)],[c_0_22, c_0_18])).
% 0.21/0.38  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_24])])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (~v2_funct_2(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_26]), c_0_16])]), c_0_27])).
% 0.21/0.38  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])]), c_0_32]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 34
% 0.21/0.38  # Proof object clause steps            : 19
% 0.21/0.38  # Proof object formula steps           : 15
% 0.21/0.38  # Proof object conjectures             : 15
% 0.21/0.38  # Proof object clause conjectures      : 12
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 12
% 0.21/0.38  # Proof object initial formulas used   : 7
% 0.21/0.38  # Proof object generating inferences   : 5
% 0.21/0.38  # Proof object simplifying inferences  : 16
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 7
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 15
% 0.21/0.38  # Removed in clause preprocessing      : 1
% 0.21/0.38  # Initial clauses in saturation        : 14
% 0.21/0.38  # Processed clauses                    : 34
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 34
% 0.21/0.38  # Other redundant clauses eliminated   : 1
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 0
% 0.21/0.38  # Generated clauses                    : 8
% 0.21/0.38  # ...of the previous two non-trivial   : 6
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 7
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 1
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 19
% 0.21/0.38  #    Positive orientable unit clauses  : 10
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 7
% 0.21/0.38  # Current number of unprocessed clauses: 0
% 0.21/0.38  # ...number of literals in the above   : 0
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 14
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 20
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 4
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 1
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 0
% 0.21/0.38  # BW rewrite match successes           : 0
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 1205
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.029 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.031 s
% 0.21/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
