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
% DateTime   : Thu Dec  3 11:04:02 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 366 expanded)
%              Number of clauses        :   21 ( 138 expanded)
%              Number of leaves         :    4 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 (1539 expanded)
%              Number of equality atoms :   43 ( 768 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(t39_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1)) = k2_relset_1(X2,X1,X3)
        & k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2)) = k1_relset_1(X2,X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(t48_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k8_relset_1(X1,X2,X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = X1 ) ) ),
    inference(assume_negation,[status(cth)],[t51_funct_2])).

fof(c_0_5,plain,(
    ! [X4,X5,X6] :
      ( ( k7_relset_1(X4,X5,X6,X4) = k2_relset_1(X4,X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
      & ( k8_relset_1(X4,X5,X6,X5) = k1_relset_1(X4,X5,X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_6,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0)) != esk1_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X7,X8,X9] :
      ( ( k7_relset_1(X8,X7,X9,k8_relset_1(X8,X7,X9,X7)) = k2_relset_1(X8,X7,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X7))) )
      & ( k8_relset_1(X8,X7,X9,k7_relset_1(X8,X7,X9,X8)) = k1_relset_1(X8,X7,X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X7))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).

cnf(c_0_8,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,plain,(
    ! [X10,X11,X12] :
      ( ( X11 = k1_xboole_0
        | k8_relset_1(X10,X11,X12,X11) = X10
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( X10 != k1_xboole_0
        | k8_relset_1(X10,X11,X12,X11) = X10
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).

cnf(c_0_11,plain,
    ( k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1)) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | k8_relset_1(X2,X1,X3,X1) = X2
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0)) != esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0)) = k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_9]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( k8_relset_1(X1,X2,esk3_0,X2) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(esk3_0,X1,X2)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0) != esk1_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( k8_relset_1(X1,X2,X3,X2) = X1
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_9]),c_0_18])]),c_0_19])).

cnf(c_0_23,plain,
    ( k8_relset_1(k1_xboole_0,X1,X2,X1) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,X1,esk3_0,X1) = k1_xboole_0
    | ~ v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9,c_0_22]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_22]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_22]),c_0_22]),c_0_24]),c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:51:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.14/0.38  # and selection function SelectCQIAr.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t51_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 0.14/0.38  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.14/0.38  fof(t39_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(k7_relset_1(X2,X1,X3,k8_relset_1(X2,X1,X3,X1))=k2_relset_1(X2,X1,X3)&k8_relset_1(X2,X1,X3,k7_relset_1(X2,X1,X3,X2))=k1_relset_1(X2,X1,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 0.14/0.38  fof(t48_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 0.14/0.38  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=X1))), inference(assume_negation,[status(cth)],[t51_funct_2])).
% 0.14/0.38  fof(c_0_5, plain, ![X4, X5, X6]:((k7_relset_1(X4,X5,X6,X4)=k2_relset_1(X4,X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))&(k8_relset_1(X4,X5,X6,X5)=k1_relset_1(X4,X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.14/0.38  fof(c_0_6, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0))!=esk1_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X7, X8, X9]:((k7_relset_1(X8,X7,X9,k8_relset_1(X8,X7,X9,X7))=k2_relset_1(X8,X7,X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X7))))&(k8_relset_1(X8,X7,X9,k7_relset_1(X8,X7,X9,X8))=k1_relset_1(X8,X7,X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X8,X7))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_relset_1])])])).
% 0.14/0.38  cnf(c_0_8, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.14/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  fof(c_0_10, plain, ![X10, X11, X12]:((X11=k1_xboole_0|k8_relset_1(X10,X11,X12,X11)=X10|(~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))&(X10!=k1_xboole_0|k8_relset_1(X10,X11,X12,X11)=X10|(~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t48_funct_2])])])).
% 0.14/0.38  cnf(c_0_11, plain, (k8_relset_1(X1,X2,X3,k7_relset_1(X1,X2,X3,X1))=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_12, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_8, c_0_9])).
% 0.14/0.38  cnf(c_0_13, plain, (X1=k1_xboole_0|k8_relset_1(X2,X1,X3,X1)=X2|~v1_funct_1(X3)|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_14, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_15, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0))!=esk1_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_16, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,k7_relset_1(esk1_0,esk2_0,esk3_0,esk1_0))=k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_9]), c_0_12])).
% 0.14/0.38  cnf(c_0_17, negated_conjecture, (k8_relset_1(X1,X2,esk3_0,X2)=X1|X2=k1_xboole_0|~v1_funct_2(esk3_0,X1,X2)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_19, negated_conjecture, (k8_relset_1(esk1_0,esk2_0,esk3_0,esk2_0)!=esk1_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.14/0.38  cnf(c_0_20, plain, (k8_relset_1(X1,X2,X3,X2)=X1|X1!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_21, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_22, negated_conjecture, (esk2_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_9]), c_0_18])]), c_0_19])).
% 0.14/0.38  cnf(c_0_23, plain, (k8_relset_1(k1_xboole_0,X1,X2,X1)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_24, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_22])])).
% 0.14/0.38  cnf(c_0_25, negated_conjecture, (k8_relset_1(k1_xboole_0,X1,esk3_0,X1)=k1_xboole_0|~v1_funct_2(esk3_0,k1_xboole_0,X1)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_23, c_0_14])).
% 0.14/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_9, c_0_22]), c_0_24])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_22]), c_0_24])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (k8_relset_1(k1_xboole_0,k1_xboole_0,esk3_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_22]), c_0_22]), c_0_24]), c_0_24])).
% 0.14/0.38  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])]), c_0_28]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 30
% 0.14/0.38  # Proof object clause steps            : 21
% 0.14/0.38  # Proof object formula steps           : 9
% 0.14/0.38  # Proof object conjectures             : 19
% 0.14/0.38  # Proof object clause conjectures      : 16
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 9
% 0.14/0.38  # Proof object initial formulas used   : 4
% 0.14/0.38  # Proof object generating inferences   : 6
% 0.14/0.38  # Proof object simplifying inferences  : 19
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 4
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 11
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 11
% 0.14/0.38  # Processed clauses                    : 35
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 0
% 0.14/0.38  # ...remaining for further processing  : 35
% 0.14/0.38  # Other redundant clauses eliminated   : 1
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 9
% 0.14/0.38  # Generated clauses                    : 13
% 0.14/0.38  # ...of the previous two non-trivial   : 21
% 0.14/0.38  # Contextual simplify-reflections      : 0
% 0.14/0.38  # Paramodulations                      : 12
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 1
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 14
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 1
% 0.14/0.38  #    Non-unit-clauses                  : 8
% 0.14/0.38  # Current number of unprocessed clauses: 4
% 0.14/0.38  # ...number of literals in the above   : 4
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 20
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 4
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 4
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.14/0.38  # Unit Clause-clause subsumption calls : 2
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 7
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 1108
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.027 s
% 0.14/0.38  # System time              : 0.005 s
% 0.14/0.38  # Total time               : 0.032 s
% 0.14/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
