%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:52 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 155 expanded)
%              Number of clauses        :   37 (  72 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  186 ( 515 expanded)
%              Number of equality atoms :   60 ( 179 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_11,plain,(
    ! [X23,X24,X25] :
      ( ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X24 = k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X23 = k1_relset_1(X23,X24,X25)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_relset_1(X23,X24,X25)
        | v1_funct_2(X25,X23,X24)
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( ~ v1_funct_2(X25,X23,X24)
        | X25 = k1_xboole_0
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != k1_xboole_0
        | v1_funct_2(X25,X23,X24)
        | X23 = k1_xboole_0
        | X24 != k1_xboole_0
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_16,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(X13,k2_zfmisc_1(k1_relat_1(X13),k2_relat_1(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ( ~ v4_relat_1(X12,X11)
        | r1_tarski(k1_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k1_relat_1(X12),X11)
        | v4_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] :
      ( ( v4_relat_1(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v5_relat_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_24,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | v1_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_26,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_29,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_relset_1(X20,X21,X22) = k1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_30,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | k1_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1) != k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_47,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_48,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_36])).

cnf(c_0_49,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_xboole_0,k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_36])])).

cnf(c_0_53,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_38]),c_0_36])]),c_0_47])).

cnf(c_0_54,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_28]),c_0_51])])).

cnf(c_0_56,negated_conjecture,
    ( ~ m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_57]),c_0_34]),c_0_51])]),c_0_58]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:33:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 7.35/7.52  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 7.35/7.52  # and selection function SelectComplexExceptUniqMaxHorn.
% 7.35/7.52  #
% 7.35/7.52  # Preprocessing time       : 0.027 s
% 7.35/7.52  # Presaturation interreduction done
% 7.35/7.52  
% 7.35/7.52  # Proof found!
% 7.35/7.52  # SZS status Theorem
% 7.35/7.52  # SZS output start CNFRefutation
% 7.35/7.52  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.35/7.52  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.35/7.52  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.35/7.52  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.35/7.52  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.35/7.52  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 7.35/7.52  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 7.35/7.52  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.35/7.52  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.35/7.52  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.35/7.52  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.35/7.52  fof(c_0_11, plain, ![X23, X24, X25]:((((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X24=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&((~v1_funct_2(X25,X23,X24)|X23=k1_relset_1(X23,X24,X25)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X23!=k1_relset_1(X23,X24,X25)|v1_funct_2(X25,X23,X24)|X23!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))))&((~v1_funct_2(X25,X23,X24)|X25=k1_xboole_0|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(X25!=k1_xboole_0|v1_funct_2(X25,X23,X24)|X23=k1_xboole_0|X24!=k1_xboole_0|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 7.35/7.52  fof(c_0_12, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 7.35/7.52  fof(c_0_13, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.35/7.52  fof(c_0_14, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 7.35/7.52  fof(c_0_15, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 7.35/7.52  cnf(c_0_16, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.35/7.52  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 7.35/7.52  fof(c_0_18, plain, ![X13]:(~v1_relat_1(X13)|r1_tarski(X13,k2_zfmisc_1(k1_relat_1(X13),k2_relat_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 7.35/7.52  fof(c_0_19, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 7.35/7.52  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.35/7.52  cnf(c_0_21, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 7.35/7.52  fof(c_0_22, plain, ![X11, X12]:((~v4_relat_1(X12,X11)|r1_tarski(k1_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k1_relat_1(X12),X11)|v4_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 7.35/7.52  fof(c_0_23, plain, ![X17, X18, X19]:((v4_relat_1(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(v5_relat_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 7.35/7.52  cnf(c_0_24, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.35/7.52  fof(c_0_25, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|v1_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 7.35/7.52  cnf(c_0_26, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 7.35/7.52  cnf(c_0_27, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 7.35/7.52  cnf(c_0_28, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.35/7.52  fof(c_0_29, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_relset_1(X20,X21,X22)=k1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 7.35/7.52  fof(c_0_30, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 7.35/7.52  cnf(c_0_31, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 7.35/7.52  cnf(c_0_32, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 7.35/7.52  cnf(c_0_33, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.35/7.52  cnf(c_0_34, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_24])).
% 7.35/7.52  cnf(c_0_35, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 7.35/7.52  cnf(c_0_36, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_26])).
% 7.35/7.52  cnf(c_0_37, plain, (k2_relat_1(X1)=k1_xboole_0|v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|k1_relset_1(k1_relat_1(X1),k2_relat_1(X1),X1)!=k1_relat_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 7.35/7.52  cnf(c_0_38, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 7.35/7.52  cnf(c_0_39, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.35/7.52  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.35/7.52  cnf(c_0_41, plain, (k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 7.35/7.52  cnf(c_0_42, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 7.35/7.52  cnf(c_0_43, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 7.35/7.52  cnf(c_0_44, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.35/7.52  cnf(c_0_45, plain, (k2_relat_1(X1)=k1_xboole_0|v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_35])).
% 7.35/7.52  cnf(c_0_46, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 7.35/7.52  cnf(c_0_47, plain, (k1_relat_1(X1)=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 7.35/7.52  cnf(c_0_48, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_36])).
% 7.35/7.52  cnf(c_0_49, plain, (k2_relat_1(X1)=k1_xboole_0|v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), inference(spm,[status(thm)],[c_0_45, c_0_17])).
% 7.35/7.52  cnf(c_0_50, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_46, c_0_17])).
% 7.35/7.52  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 7.35/7.52  cnf(c_0_52, negated_conjecture, (~v1_funct_2(esk1_0,k1_xboole_0,k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_36])])).
% 7.35/7.52  cnf(c_0_53, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_38]), c_0_36])]), c_0_47])).
% 7.35/7.52  cnf(c_0_54, plain, (k2_relat_1(X1)=k1_xboole_0|v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_28])).
% 7.35/7.52  cnf(c_0_55, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_28]), c_0_51])])).
% 7.35/7.52  cnf(c_0_56, negated_conjecture, (~m1_subset_1(esk1_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 7.35/7.52  cnf(c_0_57, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_55])).
% 7.35/7.52  cnf(c_0_58, negated_conjecture, (~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_17])).
% 7.35/7.52  cnf(c_0_59, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_57]), c_0_34]), c_0_51])]), c_0_58]), ['proof']).
% 7.35/7.52  # SZS output end CNFRefutation
% 7.35/7.52  # Proof object total steps             : 60
% 7.35/7.52  # Proof object clause steps            : 37
% 7.35/7.52  # Proof object formula steps           : 23
% 7.35/7.52  # Proof object conjectures             : 14
% 7.35/7.52  # Proof object clause conjectures      : 11
% 7.35/7.52  # Proof object formula conjectures     : 3
% 7.35/7.52  # Proof object initial clauses used    : 15
% 7.35/7.52  # Proof object initial formulas used   : 11
% 7.35/7.52  # Proof object generating inferences   : 18
% 7.35/7.52  # Proof object simplifying inferences  : 20
% 7.35/7.52  # Training examples: 0 positive, 0 negative
% 7.35/7.52  # Parsed axioms                        : 11
% 7.35/7.52  # Removed by relevancy pruning/SinE    : 0
% 7.35/7.52  # Initial clauses                      : 25
% 7.35/7.52  # Removed in clause preprocessing      : 0
% 7.35/7.52  # Initial clauses in saturation        : 25
% 7.35/7.52  # Processed clauses                    : 53760
% 7.35/7.52  # ...of these trivial                  : 0
% 7.35/7.52  # ...subsumed                          : 51885
% 7.35/7.52  # ...remaining for further processing  : 1875
% 7.35/7.52  # Other redundant clauses eliminated   : 79
% 7.35/7.52  # Clauses deleted for lack of memory   : 0
% 7.35/7.52  # Backward-subsumed                    : 408
% 7.35/7.52  # Backward-rewritten                   : 5
% 7.35/7.52  # Generated clauses                    : 1024822
% 7.35/7.52  # ...of the previous two non-trivial   : 929157
% 7.35/7.52  # Contextual simplify-reflections      : 343
% 7.35/7.52  # Paramodulations                      : 1024744
% 7.35/7.52  # Factorizations                       : 0
% 7.35/7.52  # Equation resolutions                 : 79
% 7.35/7.52  # Propositional unsat checks           : 0
% 7.35/7.52  #    Propositional check models        : 0
% 7.35/7.52  #    Propositional check unsatisfiable : 0
% 7.35/7.52  #    Propositional clauses             : 0
% 7.35/7.52  #    Propositional clauses after purity: 0
% 7.35/7.52  #    Propositional unsat core size     : 0
% 7.35/7.52  #    Propositional preprocessing time  : 0.000
% 7.35/7.52  #    Propositional encoding time       : 0.000
% 7.35/7.52  #    Propositional solver time         : 0.000
% 7.35/7.52  #    Success case prop preproc time    : 0.000
% 7.35/7.52  #    Success case prop encoding time   : 0.000
% 7.35/7.52  #    Success case prop solver time     : 0.000
% 7.35/7.52  # Current number of processed clauses  : 1430
% 7.35/7.52  #    Positive orientable unit clauses  : 26
% 7.35/7.52  #    Positive unorientable unit clauses: 0
% 7.35/7.52  #    Negative unit clauses             : 2
% 7.35/7.52  #    Non-unit-clauses                  : 1402
% 7.35/7.52  # Current number of unprocessed clauses: 869761
% 7.35/7.52  # ...number of literals in the above   : 4256351
% 7.35/7.52  # Current number of archived formulas  : 0
% 7.35/7.52  # Current number of archived clauses   : 437
% 7.35/7.52  # Clause-clause subsumption calls (NU) : 3254249
% 7.35/7.52  # Rec. Clause-clause subsumption calls : 1916879
% 7.35/7.52  # Non-unit clause-clause subsumptions  : 52609
% 7.35/7.52  # Unit Clause-clause subsumption calls : 1157
% 7.35/7.52  # Rewrite failures with RHS unbound    : 0
% 7.35/7.52  # BW rewrite match attempts            : 104
% 7.35/7.52  # BW rewrite match successes           : 1
% 7.35/7.52  # Condensation attempts                : 0
% 7.35/7.52  # Condensation successes               : 0
% 7.35/7.52  # Termbank termtop insertions          : 20576607
% 7.39/7.56  
% 7.39/7.56  # -------------------------------------------------
% 7.39/7.56  # User time                : 6.908 s
% 7.39/7.56  # System time              : 0.317 s
% 7.39/7.56  # Total time               : 7.224 s
% 7.39/7.56  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
