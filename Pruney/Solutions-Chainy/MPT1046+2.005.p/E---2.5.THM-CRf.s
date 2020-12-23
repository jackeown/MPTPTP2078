%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 298 expanded)
%              Number of clauses        :   23 ( 118 expanded)
%              Number of leaves         :    4 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 (1062 expanded)
%              Number of equality atoms :   25 ( 262 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t162_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k5_partfun1(X1,X1,k3_partfun1(X2,X1,X1)) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_2)).

fof(t87_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k3_partfun1(X3,X1,X2) = X3 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(t174_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_partfun1(X3,X1)
      <=> k5_partfun1(X1,X2,X3) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => k5_partfun1(X1,X1,k3_partfun1(X2,X1,X1)) = k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t162_funct_2])).

fof(c_0_5,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_funct_1(X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k3_partfun1(X12,X10,X11) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_partfun1])])).

fof(c_0_6,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & k5_partfun1(esk1_0,esk1_0,k3_partfun1(esk2_0,esk1_0,esk1_0)) != k1_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_7,plain,
    ( k3_partfun1(X1,X2,X3) = X1
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X4,X5,X6] :
      ( ( X5 = k1_xboole_0
        | v1_partfun1(X6,X4)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X4,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) )
      & ( X4 != k1_xboole_0
        | v1_partfun1(X6,X4)
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,X4,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

fof(c_0_10,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_partfun1(X9,X7)
        | k5_partfun1(X7,X8,X9) = k1_tarski(X9)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( k5_partfun1(X7,X8,X9) != k1_tarski(X9)
        | v1_partfun1(X9,X7)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_partfun1])])])).

cnf(c_0_11,negated_conjecture,
    ( k3_partfun1(esk2_0,X1,X2) = esk2_0
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_7,c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k5_partfun1(X2,X3,X1) = k1_tarski(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( k5_partfun1(esk1_0,esk1_0,k3_partfun1(esk2_0,esk1_0,esk1_0)) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( k3_partfun1(esk2_0,esk1_0,esk1_0) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( k5_partfun1(X1,X2,esk2_0) = k1_tarski(esk2_0)
    | ~ v1_partfun1(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( k5_partfun1(esk1_0,esk1_0,esk2_0) != k1_tarski(esk2_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( v1_partfun1(X2,X1)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(cn,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_partfun1(esk2_0,X2)
    | ~ v1_funct_2(esk2_0,X2,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_partfun1(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_20])).

cnf(c_0_25,plain,
    ( v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X1) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_12]),c_0_23])]),c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( v1_partfun1(esk2_0,k1_xboole_0)
    | ~ v1_funct_2(esk2_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_26]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_26]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_partfun1(esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_24,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.33  % Computer   : n004.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:56:23 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S076N
% 0.19/0.37  # and selection function SelectCQIAr.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.026 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t162_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k5_partfun1(X1,X1,k3_partfun1(X2,X1,X1))=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_2)).
% 0.19/0.37  fof(t87_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k3_partfun1(X3,X1,X2)=X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_partfun1)).
% 0.19/0.37  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.19/0.37  fof(t174_partfun1, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_partfun1(X3,X1)<=>k5_partfun1(X1,X2,X3)=k1_tarski(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_partfun1)).
% 0.19/0.37  fof(c_0_4, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k5_partfun1(X1,X1,k3_partfun1(X2,X1,X1))=k1_tarski(X2))), inference(assume_negation,[status(cth)],[t162_funct_2])).
% 0.19/0.37  fof(c_0_5, plain, ![X10, X11, X12]:(~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|k3_partfun1(X12,X10,X11)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_partfun1])])).
% 0.19/0.37  fof(c_0_6, negated_conjecture, (((v1_funct_1(esk2_0)&v1_funct_2(esk2_0,esk1_0,esk1_0))&m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))))&k5_partfun1(esk1_0,esk1_0,k3_partfun1(esk2_0,esk1_0,esk1_0))!=k1_tarski(esk2_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.37  cnf(c_0_7, plain, (k3_partfun1(X1,X2,X3)=X1|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.37  cnf(c_0_8, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  fof(c_0_9, plain, ![X4, X5, X6]:((X5=k1_xboole_0|v1_partfun1(X6,X4)|(~v1_funct_1(X6)|~v1_funct_2(X6,X4,X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))|(~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))))&(X4!=k1_xboole_0|v1_partfun1(X6,X4)|(~v1_funct_1(X6)|~v1_funct_2(X6,X4,X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))))|(~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.19/0.37  fof(c_0_10, plain, ![X7, X8, X9]:((~v1_partfun1(X9,X7)|k5_partfun1(X7,X8,X9)=k1_tarski(X9)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(k5_partfun1(X7,X8,X9)!=k1_tarski(X9)|v1_partfun1(X9,X7)|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t174_partfun1])])])).
% 0.19/0.37  cnf(c_0_11, negated_conjecture, (k3_partfun1(esk2_0,X1,X2)=esk2_0|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_7, c_0_8])).
% 0.19/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_13, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_14, plain, (k5_partfun1(X2,X3,X1)=k1_tarski(X1)|~v1_partfun1(X1,X2)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (k5_partfun1(esk1_0,esk1_0,k3_partfun1(esk2_0,esk1_0,esk1_0))!=k1_tarski(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_16, negated_conjecture, (k3_partfun1(esk2_0,esk1_0,esk1_0)=esk2_0), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.37  cnf(c_0_17, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.37  cnf(c_0_18, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_19, negated_conjecture, (k5_partfun1(X1,X2,esk2_0)=k1_tarski(esk2_0)|~v1_partfun1(esk2_0,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_14, c_0_8])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (k5_partfun1(esk1_0,esk1_0,esk2_0)!=k1_tarski(esk2_0)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.37  cnf(c_0_21, plain, (v1_partfun1(X2,X1)|X1!=k1_xboole_0|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(cn,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (X1=k1_xboole_0|v1_partfun1(esk2_0,X2)|~v1_funct_2(esk2_0,X2,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_18, c_0_8])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk2_0,esk1_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (~v1_partfun1(esk2_0,esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_12]), c_0_20])).
% 0.19/0.37  cnf(c_0_25, plain, (v1_partfun1(X1,k1_xboole_0)|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))|~v1_funct_1(X1)), inference(er,[status(thm)],[c_0_21])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_12]), c_0_23])]), c_0_24])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (v1_partfun1(esk2_0,k1_xboole_0)|~v1_funct_2(esk2_0,k1_xboole_0,X1)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_25, c_0_8])).
% 0.19/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_26]), c_0_26])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk2_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_26]), c_0_26])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (~v1_partfun1(esk2_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_24, c_0_26])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), c_0_30]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 32
% 0.19/0.37  # Proof object clause steps            : 23
% 0.19/0.37  # Proof object formula steps           : 9
% 0.19/0.37  # Proof object conjectures             : 19
% 0.19/0.37  # Proof object clause conjectures      : 16
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 8
% 0.19/0.37  # Proof object initial formulas used   : 4
% 0.19/0.37  # Proof object generating inferences   : 8
% 0.19/0.37  # Proof object simplifying inferences  : 16
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 4
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 9
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 9
% 0.19/0.37  # Processed clauses                    : 33
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 33
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 6
% 0.19/0.37  # Generated clauses                    : 12
% 0.19/0.37  # ...of the previous two non-trivial   : 16
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 11
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
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
% 0.19/0.37  # Current number of processed clauses  : 17
% 0.19/0.37  #    Positive orientable unit clauses  : 5
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 2
% 0.19/0.37  #    Non-unit-clauses                  : 10
% 0.19/0.37  # Current number of unprocessed clauses: 0
% 0.19/0.37  # ...number of literals in the above   : 0
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 15
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 44
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 11
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.37  # Unit Clause-clause subsumption calls : 11
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 6
% 0.19/0.37  # BW rewrite match successes           : 2
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 1090
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.026 s
% 0.19/0.37  # System time              : 0.005 s
% 0.19/0.37  # Total time               : 0.031 s
% 0.19/0.37  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
