%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0989+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:59 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 201 expanded)
%              Number of clauses        :   38 (  75 expanded)
%              Number of leaves         :   13 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 884 expanded)
%              Number of equality atoms :   77 ( 361 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',dt_k2_funct_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d9_funct_1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t65_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',fc6_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t61_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( k2_relset_1(X1,X2,X3) = X2
            & v2_funct_1(X3) )
         => ( X2 = k1_xboole_0
            | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
              & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t35_funct_2])).

fof(c_0_14,plain,(
    ! [X748,X749] :
      ( ~ v1_relat_1(X748)
      | ~ m1_subset_1(X749,k1_zfmisc_1(X748))
      | v1_relat_1(X749) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_15,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & v2_funct_1(esk3_0)
    & esk2_0 != k1_xboole_0
    & ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) != k6_partfun1(esk1_0)
      | k5_relat_1(k2_funct_1(esk3_0),esk3_0) != k6_partfun1(esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_16,plain,(
    ! [X980,X981] : v1_relat_1(k2_zfmisc_1(X980,X981)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_17,plain,(
    ! [X247] :
      ( ( v1_relat_1(k2_funct_1(X247))
        | ~ v1_relat_1(X247)
        | ~ v1_funct_1(X247) )
      & ( v1_funct_1(k2_funct_1(X247))
        | ~ v1_relat_1(X247)
        | ~ v1_funct_1(X247) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_18,plain,(
    ! [X2574] :
      ( ( k2_relat_1(X2574) = k1_relat_1(k4_relat_1(X2574))
        | ~ v1_relat_1(X2574) )
      & ( k1_relat_1(X2574) = k2_relat_1(k4_relat_1(X2574))
        | ~ v1_relat_1(X2574) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X246] :
      ( ~ v1_relat_1(X246)
      | ~ v1_funct_1(X246)
      | ~ v2_funct_1(X246)
      | k2_funct_1(X246) = k4_relat_1(X246) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_23,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X271] :
      ( ~ v1_relat_1(X271)
      | ~ v1_funct_1(X271)
      | ~ v2_funct_1(X271)
      | k2_funct_1(k2_funct_1(X271)) = X271 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_26,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_30,plain,(
    ! [X248] :
      ( ( v1_relat_1(k2_funct_1(X248))
        | ~ v1_relat_1(X248)
        | ~ v1_funct_1(X248)
        | ~ v2_funct_1(X248) )
      & ( v1_funct_1(k2_funct_1(X248))
        | ~ v1_relat_1(X248)
        | ~ v1_funct_1(X248)
        | ~ v2_funct_1(X248) )
      & ( v2_funct_1(k2_funct_1(X248))
        | ~ v1_relat_1(X248)
        | ~ v1_funct_1(X248)
        | ~ v2_funct_1(X248) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

fof(c_0_31,plain,(
    ! [X17] : k6_partfun1(X17) = k6_relat_1(X17) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_32,plain,(
    ! [X234] :
      ( ( k5_relat_1(X234,k2_funct_1(X234)) = k6_relat_1(k1_relat_1(X234))
        | ~ v2_funct_1(X234)
        | ~ v1_relat_1(X234)
        | ~ v1_funct_1(X234) )
      & ( k5_relat_1(k2_funct_1(X234),X234) = k6_relat_1(k2_relat_1(X234))
        | ~ v2_funct_1(X234)
        | ~ v1_relat_1(X234)
        | ~ v1_funct_1(X234) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k4_relat_1(esk3_0) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_29]),c_0_27])])).

cnf(c_0_37,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) != k6_partfun1(esk1_0)
    | k5_relat_1(k2_funct_1(esk3_0),esk3_0) != k6_partfun1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_40,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_27])])).

cnf(c_0_43,negated_conjecture,
    ( k2_funct_1(k2_funct_1(esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_24]),c_0_29]),c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_29]),c_0_27])])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_24]),c_0_27])])).

fof(c_0_47,plain,(
    ! [X620,X621,X622] :
      ( ~ m1_subset_1(X622,k1_zfmisc_1(k2_zfmisc_1(X620,X621)))
      | k2_relset_1(X620,X621,X622) = k2_relat_1(X622) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_48,plain,(
    ! [X3407,X3408,X3409] :
      ( ~ m1_subset_1(X3409,k1_zfmisc_1(k2_zfmisc_1(X3407,X3408)))
      | k1_relset_1(X3407,X3408,X3409) = k1_relat_1(X3409) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_49,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) != k6_relat_1(esk1_0)
    | k5_relat_1(k2_funct_1(esk3_0),esk3_0) != k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_29]),c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk3_0),esk3_0) = k6_relat_1(k2_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_52,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_54,plain,(
    ! [X1079,X1080,X1081] :
      ( ( ~ v1_funct_2(X1081,X1079,X1080)
        | X1079 = k1_relset_1(X1079,X1080,X1081)
        | X1080 = k1_xboole_0
        | ~ m1_subset_1(X1081,k1_zfmisc_1(k2_zfmisc_1(X1079,X1080))) )
      & ( X1079 != k1_relset_1(X1079,X1080,X1081)
        | v1_funct_2(X1081,X1079,X1080)
        | X1080 = k1_xboole_0
        | ~ m1_subset_1(X1081,k1_zfmisc_1(k2_zfmisc_1(X1079,X1080))) )
      & ( ~ v1_funct_2(X1081,X1079,X1080)
        | X1079 = k1_relset_1(X1079,X1080,X1081)
        | X1079 != k1_xboole_0
        | ~ m1_subset_1(X1081,k1_zfmisc_1(k2_zfmisc_1(X1079,X1080))) )
      & ( X1079 != k1_relset_1(X1079,X1080,X1081)
        | v1_funct_2(X1081,X1079,X1080)
        | X1079 != k1_xboole_0
        | ~ m1_subset_1(X1081,k1_zfmisc_1(k2_zfmisc_1(X1079,X1080))) )
      & ( ~ v1_funct_2(X1081,X1079,X1080)
        | X1081 = k1_xboole_0
        | X1079 = k1_xboole_0
        | X1080 != k1_xboole_0
        | ~ m1_subset_1(X1081,k1_zfmisc_1(k2_zfmisc_1(X1079,X1080))) )
      & ( X1081 != k1_xboole_0
        | v1_funct_2(X1081,X1079,X1080)
        | X1079 = k1_xboole_0
        | X1080 != k1_xboole_0
        | ~ m1_subset_1(X1081,k1_zfmisc_1(k2_zfmisc_1(X1079,X1080))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_55,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) != k6_relat_1(esk1_0)
    | k6_relat_1(k2_relat_1(esk3_0)) != k6_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_20]),c_0_53])).

cnf(c_0_58,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_20])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk3_0)) != k6_relat_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_63,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_20])]),c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
