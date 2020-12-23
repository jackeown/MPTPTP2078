%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:03 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :   88 (1331 expanded)
%              Number of clauses        :   62 ( 585 expanded)
%              Number of leaves         :   13 ( 318 expanded)
%              Depth                    :   19
%              Number of atoms          :  257 (5216 expanded)
%              Number of equality atoms :   70 ( 957 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    8 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t4_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k1_relat_1(X26),X24)
      | ~ r1_tarski(k2_relat_1(X26),X25)
      | m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r1_tarski(k2_relat_1(X2),X1)
         => ( v1_funct_1(X2)
            & v1_funct_2(X2,k1_relat_1(X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t4_funct_2])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_funct_1(esk2_0)
    & r1_tarski(k2_relat_1(esk2_0),esk1_0)
    & ( ~ v1_funct_1(esk2_0)
      | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
      | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
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

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

fof(c_0_27,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_funct_1(esk2_0)
    | ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_31]),c_0_23])])).

fof(c_0_36,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X29 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X29 != k1_xboole_0
        | v1_funct_2(X29,X27,X28)
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_35])).

cnf(c_0_40,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_26])])).

fof(c_0_42,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_39]),c_0_30]),c_0_23])])).

cnf(c_0_47,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0) != k1_relat_1(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_26]),c_0_41])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]),c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_46]),c_0_23])])).

cnf(c_0_54,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26])])).

cnf(c_0_55,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_30]),c_0_23])])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,X2) = X2
    | ~ r1_tarski(k1_xboole_0,X2)
    | ~ r1_tarski(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_54]),c_0_50]),c_0_55]),c_0_50]),c_0_55]),c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k1_relat_1(esk1_0))
    | ~ r1_tarski(k1_xboole_0,esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( k1_relat_1(X1) = X1
    | ~ r1_tarski(k1_xboole_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_51])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_relat_1(X1),esk1_0)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_18])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),esk1_0)
    | ~ r1_tarski(k1_xboole_0,esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_66,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | ~ r1_tarski(X16,k1_relat_1(X17))
      | k1_relat_1(k7_relat_1(X17,X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

fof(c_0_67,plain,(
    ! [X12,X13] :
      ( ~ v1_relat_1(X13)
      | ~ v4_relat_1(X13,X12)
      | X13 = k7_relat_1(X13,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,esk1_0)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_51])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_xboole_0,X1)
    | k1_relat_1(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_45]),c_0_60])])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk2_0),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_54]),c_0_54]),c_0_18]),c_0_54]),c_0_18])])).

cnf(c_0_71,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_funct_2(X1,X2,k1_xboole_0)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,esk2_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_68,c_0_54])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk2_0,k1_xboole_0,X1)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51])]),c_0_70])])).

cnf(c_0_75,plain,
    ( k1_relat_1(X1) = X2
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_50])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk1_0)))
    | ~ r1_tarski(k1_xboole_0,esk1_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_70]),c_0_18])])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | ~ v4_relat_1(k1_xboole_0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_75]),c_0_76]),c_0_58])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk2_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_54]),c_0_55]),c_0_50]),c_0_54]),c_0_18]),c_0_54]),c_0_18])])).

fof(c_0_81,plain,(
    ! [X18,X19,X20] :
      ( ( v4_relat_1(X20,X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( v5_relat_1(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v4_relat_1(k1_xboole_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_58]),c_0_18]),c_0_80])])).

cnf(c_0_83,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_18])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_76]),c_0_58]),c_0_55]),c_0_45])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_50]),c_0_86])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:58:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 7.38/7.59  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 7.38/7.59  # and selection function PSelectUnlessUniqMaxPos.
% 7.38/7.59  #
% 7.38/7.59  # Preprocessing time       : 0.028 s
% 7.38/7.59  # Presaturation interreduction done
% 7.38/7.59  
% 7.38/7.59  # Proof found!
% 7.38/7.59  # SZS status Theorem
% 7.38/7.59  # SZS output start CNFRefutation
% 7.38/7.59  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.38/7.59  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.38/7.59  fof(t4_funct_2, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 7.38/7.59  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.38/7.59  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 7.38/7.59  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.38/7.59  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.38/7.59  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.38/7.59  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.38/7.59  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 7.38/7.59  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.38/7.59  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 7.38/7.59  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.38/7.59  fof(c_0_13, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.38/7.59  fof(c_0_14, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k1_relat_1(X26),X24)|~r1_tarski(k2_relat_1(X26),X25)|m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 7.38/7.59  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.38/7.59  fof(c_0_16, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))))), inference(assume_negation,[status(cth)],[t4_funct_2])).
% 7.38/7.59  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 7.38/7.59  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 7.38/7.59  fof(c_0_19, negated_conjecture, ((v1_relat_1(esk2_0)&v1_funct_1(esk2_0))&(r1_tarski(k2_relat_1(esk2_0),esk1_0)&(~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 7.38/7.59  fof(c_0_20, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 7.38/7.59  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 7.38/7.59  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.38/7.59  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.38/7.59  fof(c_0_24, plain, ![X14, X15]:((r1_tarski(k1_relat_1(X14),k1_relat_1(X15))|~r1_tarski(X14,X15)|~v1_relat_1(X15)|~v1_relat_1(X14))&(r1_tarski(k2_relat_1(X14),k2_relat_1(X15))|~r1_tarski(X14,X15)|~v1_relat_1(X15)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 7.38/7.59  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 7.38/7.59  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 7.38/7.59  fof(c_0_27, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 7.38/7.59  cnf(c_0_28, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.38/7.59  cnf(c_0_29, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 7.38/7.59  cnf(c_0_30, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.38/7.59  cnf(c_0_31, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_23])])).
% 7.38/7.59  cnf(c_0_32, negated_conjecture, (~v1_funct_1(esk2_0)|~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.38/7.59  cnf(c_0_33, negated_conjecture, (v1_funct_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.38/7.59  fof(c_0_34, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 7.38/7.59  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_31]), c_0_23])])).
% 7.38/7.59  fof(c_0_36, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 7.38/7.59  cnf(c_0_37, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)|~m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])])).
% 7.38/7.59  cnf(c_0_38, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.38/7.59  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0))))), inference(spm,[status(thm)],[c_0_25, c_0_35])).
% 7.38/7.59  cnf(c_0_40, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 7.38/7.59  cnf(c_0_41, negated_conjecture, (~v1_funct_2(esk2_0,k1_relat_1(esk2_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_26])])).
% 7.38/7.59  fof(c_0_42, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 7.38/7.59  cnf(c_0_43, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 7.38/7.59  cnf(c_0_44, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 7.38/7.59  cnf(c_0_45, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_38])).
% 7.38/7.59  cnf(c_0_46, negated_conjecture, (r1_tarski(k2_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_39]), c_0_30]), c_0_23])])).
% 7.38/7.59  cnf(c_0_47, negated_conjecture, (esk1_0=k1_xboole_0|k1_relset_1(k1_relat_1(esk2_0),esk1_0,esk2_0)!=k1_relat_1(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_26]), c_0_41])).
% 7.38/7.59  cnf(c_0_48, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 7.38/7.59  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.38/7.59  cnf(c_0_50, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_43])).
% 7.38/7.59  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.38/7.59  cnf(c_0_52, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_44]), c_0_45])).
% 7.38/7.59  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_46]), c_0_23])])).
% 7.38/7.59  cnf(c_0_54, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_26])])).
% 7.38/7.59  cnf(c_0_55, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 7.38/7.59  cnf(c_0_56, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k1_relat_1(k2_zfmisc_1(k1_relat_1(esk2_0),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_29]), c_0_30]), c_0_23])])).
% 7.38/7.59  cnf(c_0_57, plain, (k2_zfmisc_1(X1,X2)=X2|~r1_tarski(k1_xboole_0,X2)|~r1_tarski(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 7.38/7.59  cnf(c_0_58, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 7.38/7.59  cnf(c_0_59, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X2,X3,X1)!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X2,k1_xboole_0)|~r1_tarski(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_52, c_0_51])).
% 7.38/7.59  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_54]), c_0_50]), c_0_55]), c_0_50]), c_0_55]), c_0_50])).
% 7.38/7.59  cnf(c_0_61, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k1_relat_1(esk1_0))|~r1_tarski(k1_xboole_0,esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 7.38/7.59  cnf(c_0_62, plain, (k1_relat_1(X1)=X1|~r1_tarski(k1_xboole_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_51])).
% 7.38/7.59  cnf(c_0_63, negated_conjecture, (~v1_funct_2(X1,k1_relat_1(X1),esk1_0)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_41, c_0_51])).
% 7.38/7.59  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk2_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_18])])).
% 7.38/7.59  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),esk1_0)|~r1_tarski(k1_xboole_0,esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 7.38/7.59  fof(c_0_66, plain, ![X16, X17]:(~v1_relat_1(X17)|(~r1_tarski(X16,k1_relat_1(X17))|k1_relat_1(k7_relat_1(X17,X16))=X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 7.38/7.59  fof(c_0_67, plain, ![X12, X13]:(~v1_relat_1(X13)|~v4_relat_1(X13,X12)|X13=k7_relat_1(X13,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 7.38/7.59  cnf(c_0_68, negated_conjecture, (~v1_funct_2(X1,X2,esk1_0)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_51])).
% 7.38/7.59  cnf(c_0_69, negated_conjecture, (v1_funct_2(esk2_0,k1_xboole_0,X1)|k1_relat_1(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_48]), c_0_45]), c_0_60])])).
% 7.38/7.59  cnf(c_0_70, negated_conjecture, (r1_tarski(k1_relat_1(esk2_0),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_54]), c_0_54]), c_0_18]), c_0_54]), c_0_18])])).
% 7.38/7.59  cnf(c_0_71, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 7.38/7.59  cnf(c_0_72, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 7.38/7.59  cnf(c_0_73, negated_conjecture, (~v1_funct_2(X1,X2,k1_xboole_0)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,esk2_0)|~r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[c_0_68, c_0_54])).
% 7.38/7.59  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk2_0,k1_xboole_0,X1)|~r1_tarski(k1_xboole_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51])]), c_0_70])])).
% 7.38/7.59  cnf(c_0_75, plain, (k1_relat_1(X1)=X2|~v4_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 7.38/7.59  cnf(c_0_76, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_30, c_0_50])).
% 7.38/7.59  cnf(c_0_77, negated_conjecture, (r1_tarski(esk2_0,k2_zfmisc_1(k1_relat_1(esk2_0),k2_relat_1(esk1_0)))|~r1_tarski(k1_xboole_0,esk1_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_57])).
% 7.38/7.59  cnf(c_0_78, negated_conjecture, (~r1_tarski(k1_xboole_0,k1_relat_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_70]), c_0_18])])).
% 7.38/7.59  cnf(c_0_79, plain, (X1=k1_xboole_0|~v4_relat_1(k1_xboole_0,X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_75]), c_0_76]), c_0_58])])).
% 7.38/7.59  cnf(c_0_80, negated_conjecture, (r1_tarski(esk2_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_54]), c_0_55]), c_0_50]), c_0_54]), c_0_18]), c_0_54]), c_0_18])])).
% 7.38/7.59  fof(c_0_81, plain, ![X18, X19, X20]:((v4_relat_1(X20,X18)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(v5_relat_1(X20,X19)|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 7.38/7.59  cnf(c_0_82, negated_conjecture, (~v4_relat_1(k1_xboole_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_58]), c_0_18]), c_0_80])])).
% 7.38/7.59  cnf(c_0_83, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 7.38/7.59  cnf(c_0_84, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_21, c_0_18])).
% 7.38/7.59  cnf(c_0_85, negated_conjecture, (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 7.38/7.59  cnf(c_0_86, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_76]), c_0_58]), c_0_55]), c_0_45])).
% 7.38/7.59  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_50]), c_0_86])]), ['proof']).
% 7.38/7.59  # SZS output end CNFRefutation
% 7.38/7.59  # Proof object total steps             : 88
% 7.38/7.59  # Proof object clause steps            : 62
% 7.38/7.59  # Proof object formula steps           : 26
% 7.38/7.59  # Proof object conjectures             : 35
% 7.38/7.59  # Proof object clause conjectures      : 32
% 7.38/7.59  # Proof object formula conjectures     : 3
% 7.38/7.59  # Proof object initial clauses used    : 21
% 7.38/7.59  # Proof object initial formulas used   : 13
% 7.38/7.59  # Proof object generating inferences   : 31
% 7.38/7.59  # Proof object simplifying inferences  : 71
% 7.38/7.59  # Training examples: 0 positive, 0 negative
% 7.38/7.59  # Parsed axioms                        : 13
% 7.38/7.59  # Removed by relevancy pruning/SinE    : 0
% 7.38/7.59  # Initial clauses                      : 29
% 7.38/7.59  # Removed in clause preprocessing      : 0
% 7.38/7.59  # Initial clauses in saturation        : 29
% 7.38/7.59  # Processed clauses                    : 14609
% 7.38/7.59  # ...of these trivial                  : 69
% 7.38/7.59  # ...subsumed                          : 11800
% 7.38/7.59  # ...remaining for further processing  : 2740
% 7.38/7.59  # Other redundant clauses eliminated   : 2688
% 7.38/7.59  # Clauses deleted for lack of memory   : 0
% 7.38/7.59  # Backward-subsumed                    : 518
% 7.38/7.59  # Backward-rewritten                   : 341
% 7.38/7.59  # Generated clauses                    : 922472
% 7.38/7.59  # ...of the previous two non-trivial   : 760192
% 7.38/7.59  # Contextual simplify-reflections      : 343
% 7.38/7.59  # Paramodulations                      : 919486
% 7.38/7.59  # Factorizations                       : 299
% 7.38/7.59  # Equation resolutions                 : 2688
% 7.38/7.59  # Propositional unsat checks           : 0
% 7.38/7.59  #    Propositional check models        : 0
% 7.38/7.59  #    Propositional check unsatisfiable : 0
% 7.38/7.59  #    Propositional clauses             : 0
% 7.38/7.59  #    Propositional clauses after purity: 0
% 7.38/7.59  #    Propositional unsat core size     : 0
% 7.38/7.59  #    Propositional preprocessing time  : 0.000
% 7.38/7.59  #    Propositional encoding time       : 0.000
% 7.38/7.59  #    Propositional solver time         : 0.000
% 7.38/7.59  #    Success case prop preproc time    : 0.000
% 7.38/7.59  #    Success case prop encoding time   : 0.000
% 7.38/7.59  #    Success case prop solver time     : 0.000
% 7.38/7.59  # Current number of processed clauses  : 1845
% 7.38/7.59  #    Positive orientable unit clauses  : 32
% 7.38/7.59  #    Positive unorientable unit clauses: 0
% 7.38/7.59  #    Negative unit clauses             : 9
% 7.38/7.59  #    Non-unit-clauses                  : 1804
% 7.38/7.59  # Current number of unprocessed clauses: 736441
% 7.38/7.59  # ...number of literals in the above   : 5846871
% 7.38/7.59  # Current number of archived formulas  : 0
% 7.38/7.59  # Current number of archived clauses   : 887
% 7.38/7.59  # Clause-clause subsumption calls (NU) : 530643
% 7.38/7.59  # Rec. Clause-clause subsumption calls : 274290
% 7.38/7.59  # Non-unit clause-clause subsumptions  : 11144
% 7.38/7.59  # Unit Clause-clause subsumption calls : 4517
% 7.38/7.59  # Rewrite failures with RHS unbound    : 0
% 7.38/7.59  # BW rewrite match attempts            : 463
% 7.38/7.59  # BW rewrite match successes           : 20
% 7.38/7.59  # Condensation attempts                : 0
% 7.38/7.59  # Condensation successes               : 0
% 7.38/7.59  # Termbank termtop insertions          : 20401885
% 7.47/7.62  
% 7.47/7.62  # -------------------------------------------------
% 7.47/7.62  # User time                : 6.912 s
% 7.47/7.62  # System time              : 0.365 s
% 7.47/7.62  # Total time               : 7.276 s
% 7.47/7.62  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
