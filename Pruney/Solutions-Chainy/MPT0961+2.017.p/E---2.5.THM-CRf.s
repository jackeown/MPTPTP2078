%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:53 EST 2020

% Result     : Theorem 9.18s
% Output     : CNFRefutation 9.18s
% Verified   : 
% Statistics : Number of formulae       :  144 (7877 expanded)
%              Number of clauses        :  122 (3587 expanded)
%              Number of leaves         :   11 (2115 expanded)
%              Depth                    :   29
%              Number of atoms          :  359 (22303 expanded)
%              Number of equality atoms :   74 (3861 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_11,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_14,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_15,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_19,plain,(
    ! [X13] :
      ( ~ v1_relat_1(X13)
      | r1_tarski(X13,k2_zfmisc_1(k1_relat_1(X13),k2_relat_1(X13))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_26,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(k1_relat_1(X14),k1_relat_1(X15))
        | ~ r1_tarski(X14,X15)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) )
      & ( r1_tarski(k2_relat_1(X14),k2_relat_1(X15))
        | ~ r1_tarski(X14,X15)
        | ~ v1_relat_1(X15)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_22]),c_0_24]),c_0_22])])).

cnf(c_0_31,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_32,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28])])).

cnf(c_0_38,plain,
    ( k1_relat_1(X1) = X1
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_23]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk1_0))))
    | ~ v1_relat_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk1_0)))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,plain,
    ( k2_relat_1(X1) = X1
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(k1_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_34]),c_0_36])]),c_0_39])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,k1_relat_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_39])).

cnf(c_0_45,plain,
    ( v1_relat_1(k1_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_42]),c_0_36])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(k2_zfmisc_1(esk1_0,esk1_0))))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_28])]),c_0_45])).

cnf(c_0_47,plain,
    ( k1_relat_1(X1) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_24])])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_49,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(X1)
    | ~ r1_tarski(esk1_0,X1)
    | ~ r1_tarski(X1,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_zfmisc_1(esk1_0,esk1_0)))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,plain,
    ( k2_relat_1(X1) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_53,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_50]),c_0_33])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))
    | ~ r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_23]),c_0_24])])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_22]),c_0_36])]),c_0_39])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))
    | ~ v1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_33]),c_0_28])])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,X2) = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_23]),c_0_24])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_53]),c_0_34]),c_0_53]),c_0_24])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( v1_relat_1(k2_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_60]),c_0_36])])).

fof(c_0_67,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X21 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != k1_xboole_0
        | v1_funct_2(X21,X19,X20)
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(esk1_0))
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_relat_1(esk1_0)),k1_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_65]),c_0_28])]),c_0_66])).

cnf(c_0_72,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_33])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(esk1_0)))
    | ~ v1_relat_1(k1_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( v1_relat_1(k1_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_70]),c_0_36])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_relat_1(esk1_0)),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( v1_relat_1(k1_relat_1(k2_relat_1(esk1_0)))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_71]),c_0_45])).

cnf(c_0_78,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_18])).

fof(c_0_79,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(esk1_0)))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(k2_relat_1(esk1_0))),k2_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_76]),c_0_28])]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0) != k1_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_33]),c_0_73])).

cnf(c_0_84,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_30]),c_0_64])).

cnf(c_0_86,negated_conjecture,
    ( v1_relat_1(k2_relat_1(esk1_0))
    | ~ v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( v1_relat_1(k2_relat_1(k1_relat_1(k2_relat_1(esk1_0))))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_82]),c_0_66])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,X1,X1)
    | ~ r1_tarski(k2_relat_1(esk1_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_23]),c_0_24])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))
    | ~ v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_81]),c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_52])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk1_0,k1_xboole_0)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_88]),c_0_53]),c_0_28])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k2_relat_1(k1_relat_1(esk1_0)),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_52])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,X1,X1)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_30]),c_0_24])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_96,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_18]),c_0_33])])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_23]),c_0_24])])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))),k2_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_93]),c_0_28])]),c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,X1,X1)
    | ~ r1_tarski(k2_relat_1(esk1_0),X2)
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_23]),c_0_24])])).

cnf(c_0_101,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97])])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_97])).

cnf(c_0_104,negated_conjecture,
    ( v1_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_99]),c_0_66])).

cnf(c_0_105,negated_conjecture,
    ( v1_relat_1(k2_relat_1(k1_relat_1(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_97])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_50]),c_0_33])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_52])).

cnf(c_0_108,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,X1,X1)
    | ~ r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_109,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_60])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_52]),c_0_103])])).

cnf(c_0_111,negated_conjecture,
    ( v1_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104,c_0_97])])).

cnf(c_0_112,negated_conjecture,
    ( v1_relat_1(k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_47]),c_0_97])])).

cnf(c_0_113,negated_conjecture,
    ( v1_relat_1(k2_relat_1(esk1_0))
    | ~ v1_relat_1(k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_106])).

cnf(c_0_114,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_107,c_0_47])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,X1,X1)
    | ~ r1_tarski(X1,k2_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_116,plain,
    ( X1 = X2
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_110]),c_0_111]),c_0_112])])).

cnf(c_0_118,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))
    | ~ v1_relat_1(k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))
    | ~ v1_relat_1(k2_relat_1(esk1_0))
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_106])).

cnf(c_0_119,negated_conjecture,
    ( v1_relat_1(k2_relat_1(esk1_0))
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_30]),c_0_56]),c_0_22]),c_0_36]),c_0_56]),c_0_24])])).

cnf(c_0_120,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_97])])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,X2)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0)
    | ~ r1_tarski(esk1_0,X1) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_52]),c_0_103])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_30]),c_0_56]),c_0_22]),c_0_22]),c_0_56]),c_0_22]),c_0_56]),c_0_24])]),c_0_36])]),c_0_119])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(esk1_0),X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_23]),c_0_98])).

cnf(c_0_125,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_52]),c_0_103])])).

cnf(c_0_126,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,X2)
    | ~ r1_tarski(X2,k2_relat_1(X1))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_103])])).

cnf(c_0_127,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_relat_1(k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_47]),c_0_103])])).

cnf(c_0_128,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),X1)
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_123])).

cnf(c_0_129,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_125]),c_0_103])])).

cnf(c_0_130,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_30]),c_0_56]),c_0_22]),c_0_56]),c_0_24])])).

cnf(c_0_131,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_132,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_133,negated_conjecture,
    ( r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),X1)
    | ~ r1_tarski(k1_relat_1(esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_130])).

cnf(c_0_135,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_131]),c_0_56])).

cnf(c_0_136,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_133])])).

cnf(c_0_137,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk1_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134,c_0_129])])).

cnf(c_0_138,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_135,c_0_18])).

cnf(c_0_139,negated_conjecture,
    ( ~ v1_funct_2(k2_relat_1(X1),X1,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_116]),c_0_137])])).

cnf(c_0_140,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ r1_tarski(k1_relset_1(k1_xboole_0,X2,X1),k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_138,c_0_30])).

cnf(c_0_141,negated_conjecture,
    ( ~ r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139,c_0_140]),c_0_24]),c_0_22]),c_0_22]),c_0_24])])).

cnf(c_0_142,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_84]),c_0_34]),c_0_24]),c_0_56])])).

cnf(c_0_143,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_18]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 9.18/9.35  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 9.18/9.35  # and selection function PSelectUnlessUniqMaxPos.
% 9.18/9.35  #
% 9.18/9.35  # Preprocessing time       : 0.027 s
% 9.18/9.35  # Presaturation interreduction done
% 9.18/9.35  
% 9.18/9.35  # Proof found!
% 9.18/9.35  # SZS status Theorem
% 9.18/9.35  # SZS output start CNFRefutation
% 9.18/9.35  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.18/9.35  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.18/9.35  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 9.18/9.35  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.18/9.35  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.18/9.35  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.18/9.35  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 9.18/9.35  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 9.18/9.35  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 9.18/9.35  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.18/9.35  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.18/9.35  fof(c_0_11, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 9.18/9.35  fof(c_0_12, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 9.18/9.35  fof(c_0_13, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 9.18/9.35  fof(c_0_14, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 9.18/9.35  fof(c_0_15, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 9.18/9.35  fof(c_0_16, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 9.18/9.35  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 9.18/9.35  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 9.18/9.35  fof(c_0_19, plain, ![X13]:(~v1_relat_1(X13)|r1_tarski(X13,k2_zfmisc_1(k1_relat_1(X13),k2_relat_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 9.18/9.35  fof(c_0_20, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 9.18/9.35  cnf(c_0_21, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.18/9.35  cnf(c_0_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 9.18/9.35  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.18/9.35  cnf(c_0_24, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 9.18/9.35  cnf(c_0_25, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 9.18/9.35  fof(c_0_26, plain, ![X14, X15]:((r1_tarski(k1_relat_1(X14),k1_relat_1(X15))|~r1_tarski(X14,X15)|~v1_relat_1(X15)|~v1_relat_1(X14))&(r1_tarski(k2_relat_1(X14),k2_relat_1(X15))|~r1_tarski(X14,X15)|~v1_relat_1(X15)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 9.18/9.35  cnf(c_0_27, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 9.18/9.35  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.18/9.35  cnf(c_0_29, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_21])).
% 9.18/9.35  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_22]), c_0_24]), c_0_22])])).
% 9.18/9.35  cnf(c_0_31, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 9.18/9.35  cnf(c_0_32, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.18/9.35  cnf(c_0_33, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 9.18/9.35  cnf(c_0_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 9.18/9.35  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 9.18/9.35  cnf(c_0_36, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_31, c_0_28])).
% 9.18/9.35  cnf(c_0_37, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))|~v1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_28])])).
% 9.18/9.35  cnf(c_0_38, plain, (k1_relat_1(X1)=X1|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 9.18/9.35  cnf(c_0_39, negated_conjecture, (v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_40, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk1_0))))|~v1_relat_1(k2_zfmisc_1(esk1_0,k2_relat_1(esk1_0)))|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 9.18/9.35  cnf(c_0_41, plain, (k2_relat_1(X1)=X1|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_22, c_0_35])).
% 9.18/9.35  cnf(c_0_42, plain, (r1_tarski(k1_relat_1(X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_34]), c_0_36])]), c_0_39])).
% 9.18/9.35  cnf(c_0_43, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 9.18/9.35  cnf(c_0_44, negated_conjecture, (r1_tarski(esk1_0,k1_relat_1(k2_zfmisc_1(esk1_0,esk1_0)))|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_39])).
% 9.18/9.35  cnf(c_0_45, plain, (v1_relat_1(k1_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_42]), c_0_36])])).
% 9.18/9.35  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(k2_zfmisc_1(esk1_0,esk1_0))))|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_28])]), c_0_45])).
% 9.18/9.35  cnf(c_0_47, plain, (k1_relat_1(X1)=X1|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_48, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.18/9.35  cnf(c_0_49, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 9.18/9.35  cnf(c_0_50, negated_conjecture, (v1_relat_1(X1)|~r1_tarski(esk1_0,X1)|~r1_tarski(X1,esk1_0)), inference(spm,[status(thm)],[c_0_28, c_0_23])).
% 9.18/9.35  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_zfmisc_1(esk1_0,esk1_0)))|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 9.18/9.35  cnf(c_0_52, plain, (k2_relat_1(X1)=X1|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_53, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_48])).
% 9.18/9.35  cnf(c_0_54, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.18/9.35  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 9.18/9.35  cnf(c_0_56, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_49])).
% 9.18/9.35  cnf(c_0_57, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_50]), c_0_33])])).
% 9.18/9.35  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_zfmisc_1(esk1_0,esk1_0))|~r1_tarski(k2_zfmisc_1(esk1_0,esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 9.18/9.35  cnf(c_0_59, plain, (k2_zfmisc_1(X1,X2)=X2|~r1_tarski(X2,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_60, plain, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_22]), c_0_36])]), c_0_39])).
% 9.18/9.35  cnf(c_0_61, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 9.18/9.35  cnf(c_0_62, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))|~v1_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_33]), c_0_28])])).
% 9.18/9.35  cnf(c_0_63, plain, (k2_zfmisc_1(X1,X2)=X1|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_64, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_30]), c_0_53]), c_0_34]), c_0_53]), c_0_24])])).
% 9.18/9.35  cnf(c_0_65, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 9.18/9.35  cnf(c_0_66, plain, (v1_relat_1(k2_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_60]), c_0_36])])).
% 9.18/9.35  fof(c_0_67, plain, ![X19, X20, X21]:((((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))&((~v1_funct_2(X21,X19,X20)|X21=k1_xboole_0|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X21!=k1_xboole_0|v1_funct_2(X21,X19,X20)|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 9.18/9.35  cnf(c_0_68, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_61, c_0_18])).
% 9.18/9.35  cnf(c_0_69, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(esk1_0)))|~v1_relat_1(k1_relat_1(esk1_0))|~r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 9.18/9.35  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_52])).
% 9.18/9.35  cnf(c_0_71, negated_conjecture, (r1_tarski(k1_relat_1(k2_relat_1(esk1_0)),k1_relat_1(esk1_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_65]), c_0_28])]), c_0_66])).
% 9.18/9.35  cnf(c_0_72, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 9.18/9.35  cnf(c_0_73, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_33])])).
% 9.18/9.35  cnf(c_0_74, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(esk1_0)))|~v1_relat_1(k1_relat_1(esk1_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 9.18/9.35  cnf(c_0_75, negated_conjecture, (v1_relat_1(k1_relat_1(esk1_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_70]), c_0_36])])).
% 9.18/9.35  cnf(c_0_76, negated_conjecture, (r1_tarski(k1_relat_1(k2_relat_1(esk1_0)),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_47])).
% 9.18/9.35  cnf(c_0_77, negated_conjecture, (v1_relat_1(k1_relat_1(k2_relat_1(esk1_0)))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_71]), c_0_45])).
% 9.18/9.35  cnf(c_0_78, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_72, c_0_18])).
% 9.18/9.35  fof(c_0_79, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 9.18/9.35  cnf(c_0_80, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_30])).
% 9.18/9.35  cnf(c_0_81, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k1_relat_1(esk1_0)))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 9.18/9.35  cnf(c_0_82, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(k2_relat_1(esk1_0))),k2_relat_1(esk1_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_76]), c_0_28])]), c_0_77])).
% 9.18/9.35  cnf(c_0_83, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0|k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0)!=k1_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_33]), c_0_73])).
% 9.18/9.35  cnf(c_0_84, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 9.18/9.35  cnf(c_0_85, negated_conjecture, (~v1_funct_2(esk1_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_30]), c_0_64])).
% 9.18/9.35  cnf(c_0_86, negated_conjecture, (v1_relat_1(k2_relat_1(esk1_0))|~v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_81])).
% 9.18/9.35  cnf(c_0_87, negated_conjecture, (v1_relat_1(k2_relat_1(k1_relat_1(k2_relat_1(esk1_0))))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_82]), c_0_66])).
% 9.18/9.35  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 9.18/9.35  cnf(c_0_89, negated_conjecture, (~v1_funct_2(esk1_0,X1,X1)|~r1_tarski(k2_relat_1(esk1_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_90, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))|~v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_81]), c_0_86])).
% 9.18/9.35  cnf(c_0_91, negated_conjecture, (v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_87, c_0_52])).
% 9.18/9.35  cnf(c_0_92, negated_conjecture, (r1_tarski(esk1_0,k1_xboole_0)|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_88]), c_0_53]), c_0_28])])).
% 9.18/9.35  cnf(c_0_93, negated_conjecture, (r1_tarski(k2_relat_1(k1_relat_1(esk1_0)),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_52])).
% 9.18/9.35  cnf(c_0_94, negated_conjecture, (~v1_funct_2(esk1_0,X1,X1)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_30]), c_0_24])])).
% 9.18/9.35  cnf(c_0_95, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 9.18/9.35  cnf(c_0_96, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 9.18/9.35  cnf(c_0_97, negated_conjecture, (r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_18]), c_0_33])])).
% 9.18/9.35  cnf(c_0_98, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_99, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))),k2_relat_1(esk1_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_93]), c_0_28])]), c_0_91])).
% 9.18/9.35  cnf(c_0_100, negated_conjecture, (~v1_funct_2(esk1_0,X1,X1)|~r1_tarski(k2_relat_1(esk1_0),X2)|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_23]), c_0_24])])).
% 9.18/9.35  cnf(c_0_101, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_95])).
% 9.18/9.35  cnf(c_0_102, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97])])).
% 9.18/9.35  cnf(c_0_103, negated_conjecture, (r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_98, c_0_97])).
% 9.18/9.35  cnf(c_0_104, negated_conjecture, (v1_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))|~r1_tarski(esk1_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_99]), c_0_66])).
% 9.18/9.35  cnf(c_0_105, negated_conjecture, (v1_relat_1(k2_relat_1(k1_relat_1(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_97])])).
% 9.18/9.35  cnf(c_0_106, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_50]), c_0_33])])).
% 9.18/9.35  cnf(c_0_107, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_52])).
% 9.18/9.35  cnf(c_0_108, negated_conjecture, (~v1_funct_2(esk1_0,X1,X1)|~r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(X1,k2_relat_1(esk1_0))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 9.18/9.35  cnf(c_0_109, plain, (r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_60])).
% 9.18/9.35  cnf(c_0_110, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_52]), c_0_103])])).
% 9.18/9.35  cnf(c_0_111, negated_conjecture, (v1_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_104, c_0_97])])).
% 9.18/9.35  cnf(c_0_112, negated_conjecture, (v1_relat_1(k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_47]), c_0_97])])).
% 9.18/9.35  cnf(c_0_113, negated_conjecture, (v1_relat_1(k2_relat_1(esk1_0))|~v1_relat_1(k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0)), inference(spm,[status(thm)],[c_0_25, c_0_106])).
% 9.18/9.35  cnf(c_0_114, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_107, c_0_47])).
% 9.18/9.35  cnf(c_0_115, negated_conjecture, (~v1_funct_2(esk1_0,X1,X1)|~r1_tarski(X1,k2_relat_1(esk1_0))|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 9.18/9.35  cnf(c_0_116, plain, (X1=X2|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_30, c_0_30])).
% 9.18/9.35  cnf(c_0_117, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_110]), c_0_111]), c_0_112])])).
% 9.18/9.35  cnf(c_0_118, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))|~v1_relat_1(k2_relat_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))|~v1_relat_1(k2_relat_1(esk1_0))|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)),esk1_0)), inference(spm,[status(thm)],[c_0_43, c_0_106])).
% 9.18/9.35  cnf(c_0_119, negated_conjecture, (v1_relat_1(k2_relat_1(esk1_0))|~r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_30]), c_0_56]), c_0_22]), c_0_36]), c_0_56]), c_0_24])])).
% 9.18/9.35  cnf(c_0_120, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_97])])).
% 9.18/9.35  cnf(c_0_121, negated_conjecture, (~v1_funct_2(X1,X2,X2)|~r1_tarski(X2,k2_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)|~r1_tarski(esk1_0,X1)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 9.18/9.35  cnf(c_0_122, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_relat_1(k2_relat_1(k1_relat_1(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_52]), c_0_103])])).
% 9.18/9.35  cnf(c_0_123, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k1_xboole_0)|~r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_30]), c_0_56]), c_0_22]), c_0_22]), c_0_56]), c_0_22]), c_0_56]), c_0_24])]), c_0_36])]), c_0_119])).
% 9.18/9.35  cnf(c_0_124, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k2_relat_1(esk1_0),X1)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_23]), c_0_98])).
% 9.18/9.35  cnf(c_0_125, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_52]), c_0_103])])).
% 9.18/9.35  cnf(c_0_126, negated_conjecture, (~v1_funct_2(X1,X2,X2)|~r1_tarski(X2,k2_relat_1(X1))|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_103])])).
% 9.18/9.35  cnf(c_0_127, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k2_relat_1(k2_relat_1(k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_47]), c_0_103])])).
% 9.18/9.35  cnf(c_0_128, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),X1)|~r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_123])).
% 9.18/9.35  cnf(c_0_129, negated_conjecture, (r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_125]), c_0_103])])).
% 9.18/9.35  cnf(c_0_130, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),k1_xboole_0)|~r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_30]), c_0_56]), c_0_22]), c_0_56]), c_0_24])])).
% 9.18/9.35  cnf(c_0_131, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 9.18/9.35  cnf(c_0_132, negated_conjecture, (~v1_funct_2(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(esk1_0),k2_relat_1(esk1_0))|~r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),k1_xboole_0)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 9.18/9.35  cnf(c_0_133, negated_conjecture, (r1_tarski(k2_relat_1(k2_relat_1(esk1_0)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 9.18/9.35  cnf(c_0_134, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),X1)|~r1_tarski(k1_relat_1(esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_98, c_0_130])).
% 9.18/9.35  cnf(c_0_135, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_131]), c_0_56])).
% 9.18/9.35  cnf(c_0_136, negated_conjecture, (~v1_funct_2(k2_relat_1(k2_relat_1(esk1_0)),k2_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_133])])).
% 9.18/9.35  cnf(c_0_137, negated_conjecture, (r1_tarski(k2_relat_1(esk1_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_134, c_0_129])])).
% 9.18/9.35  cnf(c_0_138, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_135, c_0_18])).
% 9.18/9.35  cnf(c_0_139, negated_conjecture, (~v1_funct_2(k2_relat_1(X1),X1,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_116]), c_0_137])])).
% 9.18/9.35  cnf(c_0_140, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~r1_tarski(k1_relset_1(k1_xboole_0,X2,X1),k1_xboole_0)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_138, c_0_30])).
% 9.18/9.35  cnf(c_0_141, negated_conjecture, (~r1_tarski(k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_139, c_0_140]), c_0_24]), c_0_22]), c_0_22]), c_0_24])])).
% 9.18/9.35  cnf(c_0_142, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141, c_0_84]), c_0_34]), c_0_24]), c_0_56])])).
% 9.18/9.35  cnf(c_0_143, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_18]), c_0_24])]), ['proof']).
% 9.18/9.35  # SZS output end CNFRefutation
% 9.18/9.35  # Proof object total steps             : 144
% 9.18/9.35  # Proof object clause steps            : 122
% 9.18/9.35  # Proof object formula steps           : 22
% 9.18/9.35  # Proof object conjectures             : 84
% 9.18/9.35  # Proof object clause conjectures      : 81
% 9.18/9.35  # Proof object formula conjectures     : 3
% 9.18/9.35  # Proof object initial clauses used    : 19
% 9.18/9.35  # Proof object initial formulas used   : 11
% 9.18/9.35  # Proof object generating inferences   : 89
% 9.18/9.35  # Proof object simplifying inferences  : 147
% 9.18/9.35  # Training examples: 0 positive, 0 negative
% 9.18/9.35  # Parsed axioms                        : 11
% 9.18/9.35  # Removed by relevancy pruning/SinE    : 0
% 9.18/9.35  # Initial clauses                      : 25
% 9.18/9.35  # Removed in clause preprocessing      : 0
% 9.18/9.35  # Initial clauses in saturation        : 25
% 9.18/9.35  # Processed clauses                    : 45681
% 9.18/9.35  # ...of these trivial                  : 184
% 9.18/9.35  # ...subsumed                          : 41341
% 9.18/9.35  # ...remaining for further processing  : 4156
% 9.18/9.35  # Other redundant clauses eliminated   : 1282
% 9.18/9.35  # Clauses deleted for lack of memory   : 0
% 9.18/9.35  # Backward-subsumed                    : 296
% 9.18/9.35  # Backward-rewritten                   : 2886
% 9.18/9.35  # Generated clauses                    : 1525089
% 9.18/9.35  # ...of the previous two non-trivial   : 1448933
% 9.18/9.35  # Contextual simplify-reflections      : 338
% 9.18/9.35  # Paramodulations                      : 1523584
% 9.18/9.35  # Factorizations                       : 224
% 9.18/9.35  # Equation resolutions                 : 1282
% 9.18/9.35  # Propositional unsat checks           : 0
% 9.18/9.35  #    Propositional check models        : 0
% 9.18/9.35  #    Propositional check unsatisfiable : 0
% 9.18/9.35  #    Propositional clauses             : 0
% 9.18/9.35  #    Propositional clauses after purity: 0
% 9.18/9.35  #    Propositional unsat core size     : 0
% 9.18/9.35  #    Propositional preprocessing time  : 0.000
% 9.18/9.35  #    Propositional encoding time       : 0.000
% 9.18/9.35  #    Propositional solver time         : 0.000
% 9.18/9.35  #    Success case prop preproc time    : 0.000
% 9.18/9.35  #    Success case prop encoding time   : 0.000
% 9.18/9.35  #    Success case prop solver time     : 0.000
% 9.18/9.35  # Current number of processed clauses  : 942
% 9.18/9.35  #    Positive orientable unit clauses  : 9
% 9.18/9.35  #    Positive unorientable unit clauses: 0
% 9.18/9.35  #    Negative unit clauses             : 3
% 9.18/9.35  #    Non-unit-clauses                  : 930
% 9.18/9.35  # Current number of unprocessed clauses: 1072037
% 9.18/9.35  # ...number of literals in the above   : 5818093
% 9.18/9.35  # Current number of archived formulas  : 0
% 9.18/9.35  # Current number of archived clauses   : 3206
% 9.18/9.35  # Clause-clause subsumption calls (NU) : 540799
% 9.18/9.35  # Rec. Clause-clause subsumption calls : 273836
% 9.18/9.35  # Non-unit clause-clause subsumptions  : 20686
% 9.18/9.35  # Unit Clause-clause subsumption calls : 46609
% 9.18/9.35  # Rewrite failures with RHS unbound    : 0
% 9.18/9.35  # BW rewrite match attempts            : 5200
% 9.18/9.35  # BW rewrite match successes           : 398
% 9.18/9.35  # Condensation attempts                : 0
% 9.18/9.35  # Condensation successes               : 0
% 9.18/9.35  # Termbank termtop insertions          : 22999049
% 9.18/9.39  
% 9.18/9.39  # -------------------------------------------------
% 9.18/9.39  # User time                : 8.587 s
% 9.18/9.39  # System time              : 0.459 s
% 9.18/9.39  # Total time               : 9.046 s
% 9.18/9.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
