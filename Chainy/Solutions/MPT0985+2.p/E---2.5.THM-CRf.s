%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0985+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 832 expanded)
%              Number of clauses        :   67 ( 325 expanded)
%              Number of leaves         :   29 ( 214 expanded)
%              Depth                    :   12
%              Number of atoms          :  366 (3311 expanded)
%              Number of equality atoms :   97 ( 500 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

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

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d9_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',dt_k2_funct_1)).

fof(redefinition_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k3_relset_1(X1,X2,X3) = k4_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k3_relset_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t37_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',cc2_relset_1)).

fof(dt_k3_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k3_relset_1(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',dt_k3_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',d18_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k1_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t113_zfmisc_1)).

fof(t77_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k5_relat_1(k6_relat_1(X1),X2) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t77_relat_1)).

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

fof(t62_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
        & k5_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t62_relat_1)).

fof(cc4_relat_1,axiom,(
    ! [X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ( v1_relat_1(X1)
        & v2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc4_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',cc1_relat_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d4_funct_1)).

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT004+2.ax',t152_zfmisc_1)).

fof(d15_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_relat_1(X1)
      <=> ! [X2] :
            ~ ( r2_hidden(X2,k1_relat_1(X1))
              & v1_xboole_0(k1_funct_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',d15_funct_1)).

fof(t67_funct_1,axiom,(
    ! [X1] : k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t67_funct_1)).

fof(t45_ordinal1,axiom,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X1)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT009+2.ax',t45_ordinal1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t81_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT007+2.ax',t60_relat_1)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT001+2.ax',d1_xboole_0)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_30,plain,(
    ! [X83,X84] :
      ( ~ v1_relat_1(X83)
      | ~ m1_subset_1(X84,k1_zfmisc_1(X83))
      | v1_relat_1(X84) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_31,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_32,plain,(
    ! [X340,X341] : v1_relat_1(k2_zfmisc_1(X340,X341)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_33,plain,(
    ! [X426] :
      ( ~ v1_relat_1(X426)
      | ~ v1_funct_1(X426)
      | ~ v2_funct_1(X426)
      | k2_funct_1(X426) = k4_relat_1(X426) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_37,plain,(
    ! [X427] :
      ( ( v1_relat_1(k2_funct_1(X427))
        | ~ v1_relat_1(X427)
        | ~ v1_funct_1(X427) )
      & ( v1_funct_1(k2_funct_1(X427))
        | ~ v1_relat_1(X427)
        | ~ v1_funct_1(X427) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_38,plain,(
    ! [X3519,X3520,X3521] :
      ( ~ m1_subset_1(X3521,k1_zfmisc_1(k2_zfmisc_1(X3519,X3520)))
      | k3_relset_1(X3519,X3520,X3521) = k4_relat_1(X3521) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k3_relset_1])])).

cnf(c_0_39,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

fof(c_0_43,plain,(
    ! [X3510] :
      ( ( k2_relat_1(X3510) = k1_relat_1(k4_relat_1(X3510))
        | ~ v1_relat_1(X3510) )
      & ( k1_relat_1(X3510) = k2_relat_1(k4_relat_1(X3510))
        | ~ v1_relat_1(X3510) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

cnf(c_0_44,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_45,plain,(
    ! [X3632,X3633,X3634] :
      ( ( v4_relat_1(X3634,X3632)
        | ~ m1_subset_1(X3634,k1_zfmisc_1(k2_zfmisc_1(X3632,X3633))) )
      & ( v5_relat_1(X3634,X3633)
        | ~ m1_subset_1(X3634,k1_zfmisc_1(k2_zfmisc_1(X3632,X3633))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_46,plain,(
    ! [X3726,X3727,X3728] :
      ( ~ m1_subset_1(X3728,k1_zfmisc_1(k2_zfmisc_1(X3726,X3727)))
      | m1_subset_1(k3_relset_1(X3726,X3727,X3728),k1_zfmisc_1(k2_zfmisc_1(X3727,X3726))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_relset_1])])).

cnf(c_0_47,plain,
    ( k3_relset_1(X2,X3,X1) = k4_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( k4_relat_1(esk3_0) = k2_funct_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_49,plain,
    ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X911,X912,X913] :
      ( ~ m1_subset_1(X913,k1_zfmisc_1(k2_zfmisc_1(X911,X912)))
      | k2_relset_1(X911,X912,X913) = k2_relat_1(X913) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_40])).

fof(c_0_52,plain,(
    ! [X3641,X3642] :
      ( ( ~ v4_relat_1(X3642,X3641)
        | r1_tarski(k1_relat_1(X3642),X3641)
        | ~ v1_relat_1(X3642) )
      & ( ~ r1_tarski(k1_relat_1(X3642),X3641)
        | v4_relat_1(X3642,X3641)
        | ~ v1_relat_1(X3642) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_53,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_54,plain,(
    ! [X3591,X3592,X3593] :
      ( ~ m1_subset_1(X3593,k1_zfmisc_1(k2_zfmisc_1(X3591,X3592)))
      | k1_relset_1(X3591,X3592,X3593) = k1_relat_1(X3593) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_55,plain,
    ( m1_subset_1(k3_relset_1(X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k3_relset_1(esk1_0,esk2_0,esk3_0) = k2_funct_1(esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_35]),c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(k4_relat_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_58,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_42])])).

fof(c_0_62,plain,(
    ! [X231,X232] :
      ( ( k2_zfmisc_1(X231,X232) != k1_xboole_0
        | X231 = k1_xboole_0
        | X232 = k1_xboole_0 )
      & ( X231 != k1_xboole_0
        | k2_zfmisc_1(X231,X232) = k1_xboole_0 )
      & ( X232 != k1_xboole_0
        | k2_zfmisc_1(X231,X232) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_63,plain,(
    ! [X2447,X2448] :
      ( ~ v1_relat_1(X2448)
      | ~ r1_tarski(k1_relat_1(X2448),X2447)
      | k5_relat_1(k6_relat_1(X2447),X2448) = X2448 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t77_relat_1])])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( v4_relat_1(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_35])).

fof(c_0_66,plain,(
    ! [X472,X473,X474] :
      ( ( ~ v1_funct_2(X474,X472,X473)
        | X472 = k1_relset_1(X472,X473,X474)
        | X473 = k1_xboole_0
        | ~ m1_subset_1(X474,k1_zfmisc_1(k2_zfmisc_1(X472,X473))) )
      & ( X472 != k1_relset_1(X472,X473,X474)
        | v1_funct_2(X474,X472,X473)
        | X473 = k1_xboole_0
        | ~ m1_subset_1(X474,k1_zfmisc_1(k2_zfmisc_1(X472,X473))) )
      & ( ~ v1_funct_2(X474,X472,X473)
        | X472 = k1_relset_1(X472,X473,X474)
        | X472 != k1_xboole_0
        | ~ m1_subset_1(X474,k1_zfmisc_1(k2_zfmisc_1(X472,X473))) )
      & ( X472 != k1_relset_1(X472,X473,X474)
        | v1_funct_2(X474,X472,X473)
        | X472 != k1_xboole_0
        | ~ m1_subset_1(X474,k1_zfmisc_1(k2_zfmisc_1(X472,X473))) )
      & ( ~ v1_funct_2(X474,X472,X473)
        | X474 = k1_xboole_0
        | X472 = k1_xboole_0
        | X473 != k1_xboole_0
        | ~ m1_subset_1(X474,k1_zfmisc_1(k2_zfmisc_1(X472,X473))) )
      & ( X474 != k1_xboole_0
        | v1_funct_2(X474,X472,X473)
        | X472 = k1_xboole_0
        | X473 != k1_xboole_0
        | ~ m1_subset_1(X474,k1_zfmisc_1(k2_zfmisc_1(X472,X473))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_67,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_35]),c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = k2_relat_1(esk3_0) ),
    inference(rw,[status(thm)],[c_0_57,c_0_48])).

cnf(c_0_70,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_35]),c_0_59])).

cnf(c_0_71,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

fof(c_0_72,plain,(
    ! [X1481] :
      ( ( k5_relat_1(k1_xboole_0,X1481) = k1_xboole_0
        | ~ v1_relat_1(X1481) )
      & ( k5_relat_1(X1481,k1_xboole_0) = k1_xboole_0
        | ~ v1_relat_1(X1481) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_relat_1])])])).

fof(c_0_73,plain,(
    ! [X4442] :
      ( ( v1_relat_1(X4442)
        | ~ v1_xboole_0(X4442)
        | ~ v1_relat_1(X4442) )
      & ( v2_relat_1(X4442)
        | ~ v1_xboole_0(X4442)
        | ~ v1_relat_1(X4442) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relat_1])])])).

fof(c_0_74,plain,(
    ! [X1032] :
      ( ~ v1_xboole_0(X1032)
      | v1_relat_1(X1032) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_75,plain,(
    ! [X597,X598,X599] :
      ( ( X599 != k1_funct_1(X597,X598)
        | r2_hidden(k4_tarski(X598,X599),X597)
        | ~ r2_hidden(X598,k1_relat_1(X597))
        | ~ v1_relat_1(X597)
        | ~ v1_funct_1(X597) )
      & ( ~ r2_hidden(k4_tarski(X598,X599),X597)
        | X599 = k1_funct_1(X597,X598)
        | ~ r2_hidden(X598,k1_relat_1(X597))
        | ~ v1_relat_1(X597)
        | ~ v1_funct_1(X597) )
      & ( X599 != k1_funct_1(X597,X598)
        | X599 = k1_xboole_0
        | r2_hidden(X598,k1_relat_1(X597))
        | ~ v1_relat_1(X597)
        | ~ v1_funct_1(X597) )
      & ( X599 != k1_xboole_0
        | X599 = k1_funct_1(X597,X598)
        | r2_hidden(X598,k1_relat_1(X597))
        | ~ v1_relat_1(X597)
        | ~ v1_funct_1(X597) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_76,plain,(
    ! [X323,X324] : ~ r2_hidden(X323,k2_zfmisc_1(X323,X324)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_77,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

fof(c_0_78,plain,(
    ! [X4444,X4445] :
      ( ( ~ v2_relat_1(X4444)
        | ~ r2_hidden(X4445,k1_relat_1(X4444))
        | ~ v1_xboole_0(k1_funct_1(X4444,X4445))
        | ~ v1_relat_1(X4444)
        | ~ v1_funct_1(X4444) )
      & ( r2_hidden(esk440_1(X4444),k1_relat_1(X4444))
        | v2_relat_1(X4444)
        | ~ v1_relat_1(X4444)
        | ~ v1_funct_1(X4444) )
      & ( v1_xboole_0(k1_funct_1(X4444,esk440_1(X4444)))
        | v2_relat_1(X4444)
        | ~ v1_relat_1(X4444)
        | ~ v1_funct_1(X4444) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_funct_1])])])])])).

cnf(c_0_79,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_80,plain,
    ( k5_relat_1(k6_relat_1(X2),X1) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_42])])).

cnf(c_0_82,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_83,negated_conjecture,
    ( k1_relset_1(esk2_0,esk1_0,k2_funct_1(esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_68])])).

cnf(c_0_85,plain,
    ( k5_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_86,plain,(
    ! [X465] : k2_funct_1(k6_relat_1(X465)) = k6_relat_1(X465) ),
    inference(variable_rename,[status(thm)],[t67_funct_1])).

cnf(c_0_87,plain,
    ( v2_relat_1(X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_88,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_89,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_90,plain,(
    ! [X3622] :
      ( v1_relat_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X3622)
      & v1_funct_1(k1_xboole_0)
      & v5_ordinal1(k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[t45_ordinal1])).

cnf(c_0_91,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_92,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_77])).

fof(c_0_93,plain,(
    ! [X469,X470,X471] :
      ( ( v1_funct_1(X471)
        | ~ v1_funct_1(X471)
        | ~ v1_partfun1(X471,X469)
        | ~ m1_subset_1(X471,k1_zfmisc_1(k2_zfmisc_1(X469,X470))) )
      & ( v1_funct_2(X471,X469,X470)
        | ~ v1_funct_1(X471)
        | ~ v1_partfun1(X471,X469)
        | ~ m1_subset_1(X471,k1_zfmisc_1(k2_zfmisc_1(X469,X470))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_94,plain,
    ( ~ v2_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) = esk2_0 ),
    inference(rw,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_40]),c_0_42])])).

cnf(c_0_97,negated_conjecture,
    ( k5_relat_1(k6_relat_1(esk1_0),esk3_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_42])])).

cnf(c_0_98,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_68])]),c_0_84])).

cnf(c_0_99,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_100,negated_conjecture,
    ( k5_relat_1(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_42])).

cnf(c_0_101,plain,
    ( k2_funct_1(k6_relat_1(X1)) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_102,plain,
    ( v2_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_103,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_104,plain,
    ( k1_funct_1(X1,X2) = k1_xboole_0
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_105,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_106,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_107,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_108,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

fof(c_0_109,plain,(
    ! [X3579,X3580,X3581] :
      ( ~ v1_xboole_0(X3579)
      | ~ m1_subset_1(X3581,k1_zfmisc_1(k2_zfmisc_1(X3579,X3580)))
      | v1_partfun1(X3581,X3579) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_110,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_111,negated_conjecture,
    ( ~ v2_relat_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k1_funct_1(k2_funct_1(esk3_0),X1))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_61]),c_0_96])])).

cnf(c_0_112,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_100])).

cnf(c_0_113,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_99])).

cnf(c_0_114,plain,
    ( v2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_115,plain,
    ( k1_funct_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_106]),c_0_107])]),c_0_108])).

fof(c_0_116,plain,(
    ! [X973,X974,X975] :
      ( ( ~ v1_xboole_0(X973)
        | ~ r2_hidden(X974,X973) )
      & ( r2_hidden(esk122_1(X975),X975)
        | v1_xboole_0(X975) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_117,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_partfun1(k2_funct_1(esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_68]),c_0_61])]),c_0_84])).

cnf(c_0_119,negated_conjecture,
    ( ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112]),c_0_113]),c_0_114]),c_0_112]),c_0_113]),c_0_115]),c_0_103])])).

cnf(c_0_120,plain,
    ( r2_hidden(esk122_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_68]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
