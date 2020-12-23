%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:45 EST 2020

% Result     : Theorem 0.61s
% Output     : CNFRefutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  118 (1511 expanded)
%              Number of clauses        :   79 ( 632 expanded)
%              Number of leaves         :   19 ( 370 expanded)
%              Depth                    :   21
%              Number of atoms          :  326 (6408 expanded)
%              Number of equality atoms :   93 (1747 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(fc23_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v4_relat_1(X3,X2) )
     => ( v1_relat_1(k7_relat_1(X3,X1))
        & v4_relat_1(k7_relat_1(X3,X1),X1)
        & v4_relat_1(k7_relat_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X3,X1)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
              & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
              & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk3_0,esk1_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X43,X44,X45,X46] :
      ( ( v1_funct_1(k2_partfun1(X43,X44,X45,X46))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( m1_subset_1(k2_partfun1(X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
        | ~ v1_funct_1(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_23,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,plain,(
    ! [X47,X48,X49,X50] :
      ( ~ v1_funct_1(X49)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | k2_partfun1(X47,X48,X49,X50) = k7_relat_1(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_27,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k1_xboole_0)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_31,plain,(
    ! [X9,X10] :
      ( ( k2_zfmisc_1(X9,X10) != k1_xboole_0
        | X9 = k1_xboole_0
        | X10 = k1_xboole_0 )
      & ( X9 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X9,X10) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_32,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_34,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_24]),c_0_25])])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_38])).

fof(c_0_45,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(k7_relat_1(X27,X26),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_46,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_47,c_0_29])).

cnf(c_0_54,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_48])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_56,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_57,plain,(
    ! [X40,X41,X42] :
      ( ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X41 = k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X40 = k1_relset_1(X40,X41,X42)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X40 != k1_relset_1(X40,X41,X42)
        | v1_funct_2(X42,X40,X41)
        | X40 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( ~ v1_funct_2(X42,X40,X41)
        | X42 = k1_xboole_0
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( X42 != k1_xboole_0
        | v1_funct_2(X42,X40,X41)
        | X40 = k1_xboole_0
        | X41 != k1_xboole_0
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_51]),c_0_52])])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_29])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

fof(c_0_62,plain,(
    ! [X36,X37,X38,X39] :
      ( ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X38)))
      | ~ r1_tarski(k1_relat_1(X39),X37)
      | m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

cnf(c_0_63,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_42])).

fof(c_0_67,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_68,plain,(
    ! [X13,X14] :
      ( ~ v1_relat_1(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_relat_1(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_70,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_38]),c_0_66])).

fof(c_0_72,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X23)
      | ~ v4_relat_1(X23,X22)
      | X23 = k7_relat_1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_73,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_74,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_75,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_25])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_47]),c_0_25])]),c_0_71])).

fof(c_0_78,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | r1_tarski(k1_relat_1(k7_relat_1(X25,X24)),X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_79,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( v4_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_25])).

cnf(c_0_81,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_25]),c_0_39])])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(esk1_0,X1) ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( k7_relat_1(esk4_0,esk1_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])])).

cnf(c_0_86,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_82,c_0_37])).

fof(c_0_87,plain,(
    ! [X17,X18,X19] :
      ( ( v1_relat_1(k7_relat_1(X19,X17))
        | ~ v1_relat_1(X19)
        | ~ v4_relat_1(X19,X18) )
      & ( v4_relat_1(k7_relat_1(X19,X17),X17)
        | ~ v1_relat_1(X19)
        | ~ v4_relat_1(X19,X18) )
      & ( v4_relat_1(k7_relat_1(X19,X17),X18)
        | ~ v1_relat_1(X19)
        | ~ v4_relat_1(X19,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_37])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_81])])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_25])).

fof(c_0_91,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | v1_relat_1(k7_relat_1(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_92,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( v4_relat_1(esk4_0,X1)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_51]),c_0_81])])).

cnf(c_0_96,plain,
    ( v4_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_97,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk4_0,X1),X1)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_81])])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_94,c_0_77])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_55,c_0_95])).

cnf(c_0_101,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,X2)
    | ~ v4_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_96]),c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( v4_relat_1(k7_relat_1(esk4_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_103,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_100]),c_0_39])])).

cnf(c_0_104,negated_conjecture,
    ( k7_relat_1(k7_relat_1(k7_relat_1(esk4_0,X1),X2),X1) = k7_relat_1(k7_relat_1(esk4_0,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103])])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,X1),esk1_0) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_80]),c_0_81])])).

cnf(c_0_106,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk4_0,X1),X1) = k7_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_107,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_108,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X29)
      | ~ r1_tarski(X28,k1_relat_1(X29))
      | k1_relat_1(k7_relat_1(X29,X28)) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(spm,[status(thm)],[c_0_69,c_0_100])).

cnf(c_0_110,negated_conjecture,
    ( r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_106]),c_0_103])])).

cnf(c_0_111,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relat_1(X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_107,c_0_63])).

cnf(c_0_112,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(X2,X3),X3,X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(X3,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_113])])).

cnf(c_0_116,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(esk4_0,X2),X2,X1)
    | ~ m1_subset_1(k7_relat_1(esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r1_tarski(X2,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_77]),c_0_81])])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_116]),c_0_113]),c_0_28])]),c_0_71]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.61/0.80  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.61/0.80  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.61/0.80  #
% 0.61/0.80  # Preprocessing time       : 0.028 s
% 0.61/0.80  # Presaturation interreduction done
% 0.61/0.80  
% 0.61/0.80  # Proof found!
% 0.61/0.80  # SZS status Theorem
% 0.61/0.80  # SZS output start CNFRefutation
% 0.61/0.80  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 0.61/0.80  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.61/0.80  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.61/0.80  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.61/0.80  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.61/0.80  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.61/0.80  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.61/0.80  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.61/0.80  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.61/0.80  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.61/0.80  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 0.61/0.80  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.61/0.80  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.61/0.80  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.61/0.80  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.61/0.80  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.61/0.80  fof(fc23_relat_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v4_relat_1(X3,X2))=>((v1_relat_1(k7_relat_1(X3,X1))&v4_relat_1(k7_relat_1(X3,X1),X1))&v4_relat_1(k7_relat_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 0.61/0.80  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.61/0.80  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.61/0.80  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 0.61/0.80  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk3_0,esk1_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.61/0.80  fof(c_0_21, plain, ![X43, X44, X45, X46]:((v1_funct_1(k2_partfun1(X43,X44,X45,X46))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(m1_subset_1(k2_partfun1(X43,X44,X45,X46),k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.61/0.80  cnf(c_0_22, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.80  cnf(c_0_23, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.61/0.80  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.80  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.80  fof(c_0_26, plain, ![X47, X48, X49, X50]:(~v1_funct_1(X49)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|k2_partfun1(X47,X48,X49,X50)=k7_relat_1(X49,X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.61/0.80  fof(c_0_27, plain, ![X8]:(~r1_tarski(X8,k1_xboole_0)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.61/0.80  cnf(c_0_28, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.80  cnf(c_0_29, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.80  fof(c_0_30, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.61/0.80  fof(c_0_31, plain, ![X9, X10]:((k2_zfmisc_1(X9,X10)!=k1_xboole_0|(X9=k1_xboole_0|X10=k1_xboole_0))&((X9!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0)&(X10!=k1_xboole_0|k2_zfmisc_1(X9,X10)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.61/0.80  fof(c_0_32, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.61/0.80  cnf(c_0_33, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 0.61/0.80  cnf(c_0_34, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.61/0.80  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.61/0.80  cnf(c_0_36, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.61/0.80  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.61/0.80  cnf(c_0_38, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.61/0.80  cnf(c_0_39, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.61/0.80  cnf(c_0_40, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.61/0.80  cnf(c_0_41, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_24]), c_0_25])])).
% 0.61/0.80  cnf(c_0_42, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.61/0.80  cnf(c_0_43, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_35, c_0_37])).
% 0.61/0.80  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_38])).
% 0.61/0.80  fof(c_0_45, plain, ![X26, X27]:(~v1_relat_1(X27)|r1_tarski(k7_relat_1(X27,X26),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.61/0.80  cnf(c_0_46, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.61/0.80  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.61/0.80  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_40])).
% 0.61/0.80  cnf(c_0_49, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.61/0.80  cnf(c_0_50, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.61/0.80  cnf(c_0_51, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.61/0.80  cnf(c_0_52, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_46])).
% 0.61/0.80  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_47, c_0_29])).
% 0.61/0.80  cnf(c_0_54, negated_conjecture, (esk4_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_48])).
% 0.61/0.80  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.61/0.80  fof(c_0_56, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.61/0.80  fof(c_0_57, plain, ![X40, X41, X42]:((((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X41=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))&((~v1_funct_2(X42,X40,X41)|X40=k1_relset_1(X40,X41,X42)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X40!=k1_relset_1(X40,X41,X42)|v1_funct_2(X42,X40,X41)|X40!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))))&((~v1_funct_2(X42,X40,X41)|X42=k1_xboole_0|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(X42!=k1_xboole_0|v1_funct_2(X42,X40,X41)|X40=k1_xboole_0|X41!=k1_xboole_0|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.61/0.80  cnf(c_0_58, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.61/0.80  cnf(c_0_59, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_51]), c_0_52])])).
% 0.61/0.80  cnf(c_0_60, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_29])).
% 0.61/0.80  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_36])).
% 0.61/0.80  fof(c_0_62, plain, ![X36, X37, X38, X39]:(~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X38)))|(~r1_tarski(k1_relat_1(X39),X37)|m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.61/0.80  cnf(c_0_63, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.61/0.80  cnf(c_0_64, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.61/0.80  cnf(c_0_65, negated_conjecture, (esk2_0!=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59]), c_0_60])).
% 0.61/0.80  cnf(c_0_66, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_42])).
% 0.61/0.80  fof(c_0_67, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.61/0.80  fof(c_0_68, plain, ![X13, X14]:(~v1_relat_1(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_relat_1(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.61/0.80  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.61/0.80  cnf(c_0_70, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.61/0.80  cnf(c_0_71, negated_conjecture, (esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_38]), c_0_66])).
% 0.61/0.80  fof(c_0_72, plain, ![X22, X23]:(~v1_relat_1(X23)|~v4_relat_1(X23,X22)|X23=k7_relat_1(X23,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.61/0.80  cnf(c_0_73, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.61/0.80  cnf(c_0_74, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.61/0.80  fof(c_0_75, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.61/0.80  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_25])).
% 0.61/0.80  cnf(c_0_77, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_47]), c_0_25])]), c_0_71])).
% 0.61/0.80  fof(c_0_78, plain, ![X24, X25]:(~v1_relat_1(X25)|r1_tarski(k1_relat_1(k7_relat_1(X25,X24)),X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.61/0.80  cnf(c_0_79, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.61/0.80  cnf(c_0_80, negated_conjecture, (v4_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_73, c_0_25])).
% 0.61/0.80  cnf(c_0_81, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_25]), c_0_39])])).
% 0.61/0.80  cnf(c_0_82, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.61/0.80  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~r1_tarski(esk1_0,X1)), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.61/0.80  cnf(c_0_84, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.61/0.80  cnf(c_0_85, negated_conjecture, (k7_relat_1(esk4_0,esk1_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])])).
% 0.61/0.80  cnf(c_0_86, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_82, c_0_37])).
% 0.61/0.80  fof(c_0_87, plain, ![X17, X18, X19]:(((v1_relat_1(k7_relat_1(X19,X17))|(~v1_relat_1(X19)|~v4_relat_1(X19,X18)))&(v4_relat_1(k7_relat_1(X19,X17),X17)|(~v1_relat_1(X19)|~v4_relat_1(X19,X18))))&(v4_relat_1(k7_relat_1(X19,X17),X18)|(~v1_relat_1(X19)|~v4_relat_1(X19,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc23_relat_1])])])).
% 0.61/0.80  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_83, c_0_37])).
% 0.61/0.80  cnf(c_0_89, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_81])])).
% 0.61/0.80  cnf(c_0_90, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_25])).
% 0.61/0.80  fof(c_0_91, plain, ![X15, X16]:(~v1_relat_1(X15)|v1_relat_1(k7_relat_1(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.61/0.80  cnf(c_0_92, plain, (v4_relat_1(k7_relat_1(X1,X2),X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.61/0.80  cnf(c_0_93, negated_conjecture, (v4_relat_1(esk4_0,X1)|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_88])).
% 0.61/0.80  cnf(c_0_94, negated_conjecture, (m1_subset_1(k1_relat_1(esk4_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_55, c_0_89])).
% 0.61/0.80  cnf(c_0_95, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(esk1_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_51]), c_0_81])])).
% 0.61/0.80  cnf(c_0_96, plain, (v4_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~v4_relat_1(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.61/0.80  cnf(c_0_97, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.61/0.80  cnf(c_0_98, negated_conjecture, (v4_relat_1(k7_relat_1(esk4_0,X1),X1)|~m1_subset_1(esk1_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_81])])).
% 0.61/0.80  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(esk1_0))), inference(rw,[status(thm)],[c_0_94, c_0_77])).
% 0.61/0.80  cnf(c_0_100, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_55, c_0_95])).
% 0.61/0.80  cnf(c_0_101, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,X2)|~v4_relat_1(X1,X3)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_96]), c_0_97])).
% 0.61/0.80  cnf(c_0_102, negated_conjecture, (v4_relat_1(k7_relat_1(esk4_0,X1),X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.61/0.80  cnf(c_0_103, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_100]), c_0_39])])).
% 0.61/0.80  cnf(c_0_104, negated_conjecture, (k7_relat_1(k7_relat_1(k7_relat_1(esk4_0,X1),X2),X1)=k7_relat_1(k7_relat_1(esk4_0,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103])])).
% 0.61/0.80  cnf(c_0_105, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,X1),esk1_0)=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_80]), c_0_81])])).
% 0.61/0.80  cnf(c_0_106, negated_conjecture, (k7_relat_1(k7_relat_1(esk4_0,X1),X1)=k7_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.61/0.80  cnf(c_0_107, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.61/0.80  fof(c_0_108, plain, ![X28, X29]:(~v1_relat_1(X29)|(~r1_tarski(X28,k1_relat_1(X29))|k1_relat_1(k7_relat_1(X29,X28))=X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.61/0.80  cnf(c_0_109, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(spm,[status(thm)],[c_0_69, c_0_100])).
% 0.61/0.80  cnf(c_0_110, negated_conjecture, (r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_106]), c_0_103])])).
% 0.61/0.80  cnf(c_0_111, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relat_1(X2)!=X3|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_107, c_0_63])).
% 0.61/0.80  cnf(c_0_112, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_108])).
% 0.61/0.80  cnf(c_0_113, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))), inference(spm,[status(thm)],[c_0_109, c_0_110])).
% 0.61/0.80  cnf(c_0_114, plain, (X1=k1_xboole_0|v1_funct_2(k7_relat_1(X2,X3),X3,X1)|~v1_relat_1(X2)|~m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(X3,k1_relat_1(X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112])])).
% 0.61/0.80  cnf(c_0_115, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_113])])).
% 0.61/0.80  cnf(c_0_116, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(k7_relat_1(esk4_0,X2),X2,X1)|~m1_subset_1(k7_relat_1(esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r1_tarski(X2,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_77]), c_0_81])])).
% 0.61/0.80  cnf(c_0_117, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_116]), c_0_113]), c_0_28])]), c_0_71]), ['proof']).
% 0.61/0.80  # SZS output end CNFRefutation
% 0.61/0.80  # Proof object total steps             : 118
% 0.61/0.80  # Proof object clause steps            : 79
% 0.61/0.80  # Proof object formula steps           : 39
% 0.61/0.80  # Proof object conjectures             : 51
% 0.61/0.80  # Proof object clause conjectures      : 48
% 0.61/0.80  # Proof object formula conjectures     : 3
% 0.61/0.80  # Proof object initial clauses used    : 28
% 0.61/0.80  # Proof object initial formulas used   : 19
% 0.61/0.80  # Proof object generating inferences   : 47
% 0.61/0.80  # Proof object simplifying inferences  : 46
% 0.61/0.80  # Training examples: 0 positive, 0 negative
% 0.61/0.80  # Parsed axioms                        : 19
% 0.61/0.80  # Removed by relevancy pruning/SinE    : 0
% 0.61/0.80  # Initial clauses                      : 36
% 0.61/0.80  # Removed in clause preprocessing      : 0
% 0.61/0.80  # Initial clauses in saturation        : 36
% 0.61/0.80  # Processed clauses                    : 7057
% 0.61/0.80  # ...of these trivial                  : 114
% 0.61/0.80  # ...subsumed                          : 5887
% 0.61/0.80  # ...remaining for further processing  : 1056
% 0.61/0.80  # Other redundant clauses eliminated   : 4
% 0.61/0.80  # Clauses deleted for lack of memory   : 0
% 0.61/0.80  # Backward-subsumed                    : 105
% 0.61/0.80  # Backward-rewritten                   : 60
% 0.61/0.80  # Generated clauses                    : 36574
% 0.61/0.80  # ...of the previous two non-trivial   : 28025
% 0.61/0.80  # Contextual simplify-reflections      : 99
% 0.61/0.80  # Paramodulations                      : 36559
% 0.61/0.80  # Factorizations                       : 0
% 0.61/0.80  # Equation resolutions                 : 15
% 0.61/0.80  # Propositional unsat checks           : 0
% 0.61/0.80  #    Propositional check models        : 0
% 0.61/0.80  #    Propositional check unsatisfiable : 0
% 0.61/0.80  #    Propositional clauses             : 0
% 0.61/0.80  #    Propositional clauses after purity: 0
% 0.61/0.80  #    Propositional unsat core size     : 0
% 0.61/0.80  #    Propositional preprocessing time  : 0.000
% 0.61/0.80  #    Propositional encoding time       : 0.000
% 0.61/0.80  #    Propositional solver time         : 0.000
% 0.61/0.80  #    Success case prop preproc time    : 0.000
% 0.61/0.80  #    Success case prop encoding time   : 0.000
% 0.61/0.80  #    Success case prop solver time     : 0.000
% 0.61/0.80  # Current number of processed clauses  : 856
% 0.61/0.80  #    Positive orientable unit clauses  : 108
% 0.61/0.80  #    Positive unorientable unit clauses: 0
% 0.61/0.80  #    Negative unit clauses             : 11
% 0.61/0.80  #    Non-unit-clauses                  : 737
% 0.61/0.80  # Current number of unprocessed clauses: 20412
% 0.61/0.80  # ...number of literals in the above   : 80455
% 0.61/0.80  # Current number of archived formulas  : 0
% 0.61/0.80  # Current number of archived clauses   : 200
% 0.61/0.80  # Clause-clause subsumption calls (NU) : 102493
% 0.61/0.80  # Rec. Clause-clause subsumption calls : 68861
% 0.61/0.80  # Non-unit clause-clause subsumptions  : 2730
% 0.61/0.80  # Unit Clause-clause subsumption calls : 1006
% 0.61/0.80  # Rewrite failures with RHS unbound    : 0
% 0.61/0.80  # BW rewrite match attempts            : 294
% 0.61/0.80  # BW rewrite match successes           : 38
% 0.61/0.80  # Condensation attempts                : 0
% 0.61/0.80  # Condensation successes               : 0
% 0.61/0.80  # Termbank termtop insertions          : 594119
% 0.61/0.80  
% 0.61/0.80  # -------------------------------------------------
% 0.61/0.80  # User time                : 0.440 s
% 0.61/0.80  # System time              : 0.017 s
% 0.61/0.80  # Total time               : 0.456 s
% 0.61/0.80  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
