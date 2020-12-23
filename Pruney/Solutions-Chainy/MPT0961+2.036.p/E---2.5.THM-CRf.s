%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:56 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 167 expanded)
%              Number of clauses        :   34 (  80 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 569 expanded)
%              Number of equality atoms :   56 ( 210 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_9,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_10,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_11,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k1_relset_1(X14,X15,X16) = k1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_12,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r1_tarski(k1_relat_1(X19),X17)
      | ~ r1_tarski(k2_relat_1(X19),X18)
      | m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | m1_subset_1(k1_relset_1(X11,X12,X13),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_21,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_relat_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ( ~ v1_funct_2(X22,X20,X21)
        | X20 = k1_relset_1(X20,X21,X22)
        | X21 = k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_relset_1(X20,X21,X22)
        | v1_funct_2(X22,X20,X21)
        | X21 = k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_2(X22,X20,X21)
        | X20 = k1_relset_1(X20,X21,X22)
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X20 != k1_relset_1(X20,X21,X22)
        | v1_funct_2(X22,X20,X21)
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( ~ v1_funct_2(X22,X20,X21)
        | X22 = k1_xboole_0
        | X20 = k1_xboole_0
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( X22 != k1_xboole_0
        | v1_funct_2(X22,X20,X21)
        | X20 = k1_xboole_0
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_17])])).

fof(c_0_29,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_30,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k1_relset_1(k1_relat_1(X1),X2,X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,k1_relat_1(X2),X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k2_relat_1(X2),X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_31])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_43,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]),c_0_17])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_41]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_xboole_0,k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_42]),c_0_17])])).

cnf(c_0_48,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_23]),c_0_42])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_41]),c_0_36])]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.54/0.73  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.54/0.73  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.54/0.73  #
% 0.54/0.73  # Preprocessing time       : 0.028 s
% 0.54/0.73  # Presaturation interreduction done
% 0.54/0.73  
% 0.54/0.73  # Proof found!
% 0.54/0.73  # SZS status Theorem
% 0.54/0.73  # SZS output start CNFRefutation
% 0.54/0.73  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.54/0.73  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.54/0.73  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.54/0.73  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.54/0.73  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.54/0.73  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.54/0.73  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.54/0.73  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.54/0.73  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.54/0.73  fof(c_0_9, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.54/0.73  fof(c_0_10, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.54/0.73  fof(c_0_11, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k1_relset_1(X14,X15,X16)=k1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.54/0.73  cnf(c_0_12, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.54/0.73  fof(c_0_13, plain, ![X17, X18, X19]:(~v1_relat_1(X19)|(~r1_tarski(k1_relat_1(X19),X17)|~r1_tarski(k2_relat_1(X19),X18)|m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.54/0.73  cnf(c_0_14, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.54/0.73  fof(c_0_15, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|m1_subset_1(k1_relset_1(X11,X12,X13),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.54/0.73  cnf(c_0_16, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.54/0.73  cnf(c_0_17, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_12])).
% 0.54/0.73  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.54/0.73  cnf(c_0_19, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_14])).
% 0.54/0.73  fof(c_0_20, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 0.54/0.73  fof(c_0_21, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.54/0.73  cnf(c_0_22, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.54/0.73  cnf(c_0_23, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_relat_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.54/0.73  fof(c_0_24, plain, ![X20, X21, X22]:((((~v1_funct_2(X22,X20,X21)|X20=k1_relset_1(X20,X21,X22)|X21=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X20!=k1_relset_1(X20,X21,X22)|v1_funct_2(X22,X20,X21)|X21=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&((~v1_funct_2(X22,X20,X21)|X20=k1_relset_1(X20,X21,X22)|X20!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X20!=k1_relset_1(X20,X21,X22)|v1_funct_2(X22,X20,X21)|X20!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))))&((~v1_funct_2(X22,X20,X21)|X22=k1_xboole_0|X20=k1_xboole_0|X21!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(X22!=k1_xboole_0|v1_funct_2(X22,X20,X21)|X20=k1_xboole_0|X21!=k1_xboole_0|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.54/0.73  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.54/0.73  fof(c_0_26, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.54/0.73  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.54/0.73  cnf(c_0_28, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(k1_xboole_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_17])])).
% 0.54/0.73  fof(c_0_29, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.54/0.73  cnf(c_0_30, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.54/0.73  cnf(c_0_31, plain, (k1_relset_1(k1_relat_1(X1),X2,X1)=k1_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_25])).
% 0.54/0.73  cnf(c_0_32, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.73  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.73  cnf(c_0_34, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.54/0.73  cnf(c_0_35, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.54/0.73  cnf(c_0_36, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.54/0.73  cnf(c_0_37, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.54/0.73  cnf(c_0_38, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.54/0.73  cnf(c_0_39, plain, (X1=k1_xboole_0|v1_funct_2(X2,k1_relat_1(X2),X1)|~v1_relat_1(X2)|~r1_tarski(k2_relat_1(X2),X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_25]), c_0_31])).
% 0.54/0.73  cnf(c_0_40, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])])).
% 0.54/0.73  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.54/0.73  cnf(c_0_42, plain, (k1_relat_1(X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.54/0.73  cnf(c_0_43, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_37]), c_0_17])).
% 0.54/0.73  cnf(c_0_44, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 0.54/0.73  cnf(c_0_45, plain, (k2_relat_1(X1)=k1_xboole_0|v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_39, c_0_19])).
% 0.54/0.73  cnf(c_0_46, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_25]), c_0_41]), c_0_19])])).
% 0.54/0.73  cnf(c_0_47, negated_conjecture, (~v1_funct_2(esk1_0,k1_xboole_0,k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_42]), c_0_17])])).
% 0.54/0.73  cnf(c_0_48, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_23]), c_0_42])).
% 0.54/0.73  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_44])).
% 0.54/0.73  cnf(c_0_50, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_41]), c_0_46])).
% 0.54/0.73  cnf(c_0_51, negated_conjecture, (~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.54/0.73  cnf(c_0_52, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_41]), c_0_36])]), c_0_51]), ['proof']).
% 0.54/0.73  # SZS output end CNFRefutation
% 0.54/0.73  # Proof object total steps             : 53
% 0.54/0.73  # Proof object clause steps            : 34
% 0.54/0.73  # Proof object formula steps           : 19
% 0.54/0.73  # Proof object conjectures             : 12
% 0.54/0.73  # Proof object clause conjectures      : 9
% 0.54/0.73  # Proof object formula conjectures     : 3
% 0.54/0.73  # Proof object initial clauses used    : 14
% 0.54/0.73  # Proof object initial formulas used   : 9
% 0.54/0.73  # Proof object generating inferences   : 15
% 0.54/0.73  # Proof object simplifying inferences  : 23
% 0.54/0.73  # Training examples: 0 positive, 0 negative
% 0.54/0.73  # Parsed axioms                        : 9
% 0.54/0.73  # Removed by relevancy pruning/SinE    : 0
% 0.54/0.73  # Initial clauses                      : 21
% 0.54/0.73  # Removed in clause preprocessing      : 0
% 0.54/0.73  # Initial clauses in saturation        : 21
% 0.54/0.73  # Processed clauses                    : 2472
% 0.54/0.73  # ...of these trivial                  : 1
% 0.54/0.73  # ...subsumed                          : 2183
% 0.54/0.73  # ...remaining for further processing  : 288
% 0.54/0.73  # Other redundant clauses eliminated   : 129
% 0.54/0.73  # Clauses deleted for lack of memory   : 0
% 0.54/0.73  # Backward-subsumed                    : 35
% 0.54/0.73  # Backward-rewritten                   : 13
% 0.54/0.73  # Generated clauses                    : 47999
% 0.54/0.73  # ...of the previous two non-trivial   : 35823
% 0.54/0.73  # Contextual simplify-reflections      : 13
% 0.54/0.73  # Paramodulations                      : 47871
% 0.54/0.73  # Factorizations                       : 0
% 0.54/0.73  # Equation resolutions                 : 129
% 0.54/0.73  # Propositional unsat checks           : 0
% 0.54/0.73  #    Propositional check models        : 0
% 0.54/0.73  #    Propositional check unsatisfiable : 0
% 0.54/0.73  #    Propositional clauses             : 0
% 0.54/0.73  #    Propositional clauses after purity: 0
% 0.54/0.73  #    Propositional unsat core size     : 0
% 0.54/0.73  #    Propositional preprocessing time  : 0.000
% 0.54/0.73  #    Propositional encoding time       : 0.000
% 0.54/0.73  #    Propositional solver time         : 0.000
% 0.54/0.73  #    Success case prop preproc time    : 0.000
% 0.54/0.73  #    Success case prop encoding time   : 0.000
% 0.54/0.73  #    Success case prop solver time     : 0.000
% 0.54/0.73  # Current number of processed clauses  : 211
% 0.54/0.73  #    Positive orientable unit clauses  : 15
% 0.54/0.73  #    Positive unorientable unit clauses: 0
% 0.54/0.73  #    Negative unit clauses             : 2
% 0.54/0.73  #    Non-unit-clauses                  : 194
% 0.54/0.73  # Current number of unprocessed clauses: 33086
% 0.54/0.73  # ...number of literals in the above   : 135317
% 0.54/0.73  # Current number of archived formulas  : 0
% 0.54/0.73  # Current number of archived clauses   : 68
% 0.54/0.73  # Clause-clause subsumption calls (NU) : 37828
% 0.54/0.73  # Rec. Clause-clause subsumption calls : 21562
% 0.54/0.73  # Non-unit clause-clause subsumptions  : 2038
% 0.54/0.73  # Unit Clause-clause subsumption calls : 159
% 0.54/0.73  # Rewrite failures with RHS unbound    : 0
% 0.54/0.73  # BW rewrite match attempts            : 26
% 0.54/0.73  # BW rewrite match successes           : 5
% 0.54/0.73  # Condensation attempts                : 0
% 0.54/0.73  # Condensation successes               : 0
% 0.54/0.73  # Termbank termtop insertions          : 852103
% 0.54/0.73  
% 0.54/0.73  # -------------------------------------------------
% 0.54/0.73  # User time                : 0.372 s
% 0.54/0.73  # System time              : 0.013 s
% 0.54/0.73  # Total time               : 0.384 s
% 0.54/0.73  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
