%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0964+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:07:59 EST 2020

% Result     : Theorem 32.87s
% Output     : CNFRefutation 32.87s
% Verified   : 
% Statistics : Number of formulae       :   34 (  61 expanded)
%              Number of clauses        :   19 (  22 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 254 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT011+2.ax',redefinition_k2_relset_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT008+2.ax',t12_funct_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r2_hidden(X3,X1)
         => ( X2 = k1_xboole_0
            | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_funct_2])).

fof(c_0_8,plain,(
    ! [X2705,X2706,X2707] :
      ( ~ m1_subset_1(X2707,k1_zfmisc_1(k2_zfmisc_1(X2705,X2706)))
      | k1_relset_1(X2705,X2706,X2707) = k1_relat_1(X2707) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_9,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r2_hidden(esk3_0,esk1_0)
    & esk2_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk4_0,esk3_0),k2_relset_1(esk1_0,esk2_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_10,plain,(
    ! [X1242,X1243,X1244] :
      ( ( ~ v1_funct_2(X1244,X1242,X1243)
        | X1242 = k1_relset_1(X1242,X1243,X1244)
        | X1243 = k1_xboole_0
        | ~ m1_subset_1(X1244,k1_zfmisc_1(k2_zfmisc_1(X1242,X1243))) )
      & ( X1242 != k1_relset_1(X1242,X1243,X1244)
        | v1_funct_2(X1244,X1242,X1243)
        | X1243 = k1_xboole_0
        | ~ m1_subset_1(X1244,k1_zfmisc_1(k2_zfmisc_1(X1242,X1243))) )
      & ( ~ v1_funct_2(X1244,X1242,X1243)
        | X1242 = k1_relset_1(X1242,X1243,X1244)
        | X1242 != k1_xboole_0
        | ~ m1_subset_1(X1244,k1_zfmisc_1(k2_zfmisc_1(X1242,X1243))) )
      & ( X1242 != k1_relset_1(X1242,X1243,X1244)
        | v1_funct_2(X1244,X1242,X1243)
        | X1242 != k1_xboole_0
        | ~ m1_subset_1(X1244,k1_zfmisc_1(k2_zfmisc_1(X1242,X1243))) )
      & ( ~ v1_funct_2(X1244,X1242,X1243)
        | X1244 = k1_xboole_0
        | X1242 = k1_xboole_0
        | X1243 != k1_xboole_0
        | ~ m1_subset_1(X1244,k1_zfmisc_1(k2_zfmisc_1(X1242,X1243))) )
      & ( X1244 != k1_xboole_0
        | v1_funct_2(X1244,X1242,X1243)
        | X1242 = k1_xboole_0
        | X1243 != k1_xboole_0
        | ~ m1_subset_1(X1244,k1_zfmisc_1(k2_zfmisc_1(X1242,X1243))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_11,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,plain,(
    ! [X1023,X1024] :
      ( ~ v1_relat_1(X1023)
      | ~ m1_subset_1(X1024,k1_zfmisc_1(X1023))
      | v1_relat_1(X1024) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_14,plain,(
    ! [X1154,X1155] : v1_relat_1(k2_zfmisc_1(X1154,X1155)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_15,plain,(
    ! [X657,X658,X659] :
      ( ~ m1_subset_1(X659,k1_zfmisc_1(k2_zfmisc_1(X657,X658)))
      | k2_relset_1(X657,X658,X659) = k2_relat_1(X659) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_16,plain,(
    ! [X468,X469] :
      ( ~ v1_relat_1(X469)
      | ~ v1_funct_1(X469)
      | ~ r2_hidden(X468,k1_relat_1(X469))
      | r2_hidden(k1_funct_1(X469,X468),k2_relat_1(X469)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_17,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_12])]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_12]),c_0_22])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk3_0),k2_relset_1(esk1_0,esk2_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),k2_relat_1(esk4_0))
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk4_0,esk3_0),k2_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
