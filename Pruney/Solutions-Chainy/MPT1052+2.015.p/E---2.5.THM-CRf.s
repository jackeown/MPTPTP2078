%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  117 (37058 expanded)
%              Number of clauses        :   82 (16858 expanded)
%              Number of leaves         :   18 (9103 expanded)
%              Depth                    :   22
%              Number of atoms          :  291 (105693 expanded)
%              Number of equality atoms :  137 (36038 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(t160_funct_2,axiom,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(l32_xboole_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,X2) = k1_xboole_0
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(fc3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

fof(c_0_19,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ r2_hidden(X33,k1_funct_2(X31,X32)) )
      & ( v1_funct_2(X33,X31,X32)
        | ~ r2_hidden(X33,k1_funct_2(X31,X32)) )
      & ( m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ r2_hidden(X33,k1_funct_2(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

fof(c_0_20,plain,(
    ! [X34,X35] : k5_partfun1(X34,X35,k3_partfun1(k1_xboole_0,X34,X35)) = k1_funct_2(X34,X35) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_21,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))
    & ( k1_relat_1(esk4_0) != esk2_0
      | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X21,X22] :
      ( ( r1_tarski(k1_relat_1(X21),k1_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r1_tarski(k2_relat_1(X21),k2_relat_1(X22))
        | ~ r1_tarski(X21,X22)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_27,plain,(
    ! [X19,X20] :
      ( ( k1_relat_1(k2_zfmisc_1(X19,X20)) = X19
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X19,X20)) = X20
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

fof(c_0_28,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk4_0,k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_23])).

fof(c_0_32,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X28 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != k1_xboole_0
        | v1_funct_2(X28,X26,X27)
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_33,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_39,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_40,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

fof(c_0_42,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k2_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_41])])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | ~ r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | k1_xboole_0 = esk2_0
    | r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_38])])).

fof(c_0_52,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_53,plain,(
    ! [X9,X10] :
      ( ( k4_xboole_0(X9,X10) != k1_xboole_0
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | k4_xboole_0(X9,X10) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | k1_xboole_0 = esk3_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_57,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_60,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | esk3_0 != esk2_0 ),
    inference(ef,[status(thm)],[c_0_55])).

cnf(c_0_62,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,plain,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_59]),c_0_60])])).

fof(c_0_65,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_66,negated_conjecture,
    ( k2_zfmisc_1(X1,esk3_0) = esk3_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,negated_conjecture,
    ( k4_xboole_0(X1,esk2_0) = X1
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_69,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | esk3_0 = X1
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | r1_tarski(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( X1 = k1_xboole_0
    | esk3_0 != esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk4_0) != esk2_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_69]),c_0_70]),c_0_45])])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = esk4_0
    | k1_xboole_0 = esk2_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_77,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_78,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( esk2_0 = X1
    | esk3_0 != esk2_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_61])).

cnf(c_0_80,negated_conjecture,
    ( k1_xboole_0 = esk3_0
    | ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_51])).

cnf(c_0_81,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | esk3_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk4_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( esk2_0 = esk4_0
    | esk3_0 != esk2_0 ),
    inference(spm,[status(thm)],[c_0_79,c_0_74])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 = esk4_0
    | esk3_0 = esk2_0
    | ~ r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = esk4_0
    | r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( esk3_0 != esk2_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_82]),c_0_83]),c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87])).

fof(c_0_89,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | ~ v1_xboole_0(X30)
      | v1_xboole_0(k1_funct_2(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

fof(c_0_90,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_91,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | k1_xboole_0 = esk2_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_88])).

cnf(c_0_92,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_93,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( k4_xboole_0(X1,esk2_0) = X1
    | k1_xboole_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,X1) = esk2_0
    | k1_xboole_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_62,c_0_91])).

fof(c_0_97,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_98,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_92,c_0_23])).

cnf(c_0_99,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_100,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_93,c_0_31])).

cnf(c_0_101,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | X1 = k1_xboole_0
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_94])).

cnf(c_0_102,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | r1_tarski(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_103,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_104,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_55])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(k1_xboole_0,esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_88]),c_0_88])).

cnf(c_0_107,negated_conjecture,
    ( k1_xboole_0 = esk4_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,plain,
    ( k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_105,c_0_88])).

cnf(c_0_110,negated_conjecture,
    ( esk2_0 != esk4_0 ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(esk4_0,esk2_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,plain,
    ( k5_partfun1(X1,esk4_0,k3_partfun1(esk4_0,X1,esk4_0)) = esk4_0
    | v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_107]),c_0_107]),c_0_107]),c_0_107])).

cnf(c_0_113,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_107]),c_0_110])).

cnf(c_0_114,plain,
    ( X1 = esk4_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_103,c_0_107])).

cnf(c_0_115,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_110]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.41  #
% 0.13/0.41  # Preprocessing time       : 0.028 s
% 0.13/0.41  # Presaturation interreduction done
% 0.13/0.41  
% 0.13/0.41  # Proof found!
% 0.13/0.41  # SZS status Theorem
% 0.13/0.41  # SZS output start CNFRefutation
% 0.13/0.41  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 0.13/0.41  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.13/0.41  fof(t160_funct_2, axiom, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_2)).
% 0.13/0.41  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.13/0.41  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.13/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.41  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.41  fof(l32_xboole_1, axiom, ![X1, X2]:(k4_xboole_0(X1,X2)=k1_xboole_0<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 0.13/0.41  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.41  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.13/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.41  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.41  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.13/0.41  fof(c_0_19, plain, ![X31, X32, X33]:(((v1_funct_1(X33)|~r2_hidden(X33,k1_funct_2(X31,X32)))&(v1_funct_2(X33,X31,X32)|~r2_hidden(X33,k1_funct_2(X31,X32))))&(m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~r2_hidden(X33,k1_funct_2(X31,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.13/0.41  fof(c_0_20, plain, ![X34, X35]:k5_partfun1(X34,X35,k3_partfun1(k1_xboole_0,X34,X35))=k1_funct_2(X34,X35), inference(variable_rename,[status(thm)],[t160_funct_2])).
% 0.13/0.41  fof(c_0_21, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&(r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))&(k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.13/0.41  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  cnf(c_0_23, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.41  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,k1_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_25, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.41  fof(c_0_26, plain, ![X21, X22]:((r1_tarski(k1_relat_1(X21),k1_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r1_tarski(k2_relat_1(X21),k2_relat_1(X22))|~r1_tarski(X21,X22)|~v1_relat_1(X22)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.13/0.41  fof(c_0_27, plain, ![X19, X20]:((k1_relat_1(k2_zfmisc_1(X19,X20))=X19|(X19=k1_xboole_0|X20=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X19,X20))=X20|(X19=k1_xboole_0|X20=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.13/0.41  fof(c_0_28, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.41  fof(c_0_29, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.41  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(esk4_0,k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0)))), inference(rw,[status(thm)],[c_0_24, c_0_23])).
% 0.13/0.41  fof(c_0_32, plain, ![X26, X27, X28]:((((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&((~v1_funct_2(X28,X26,X27)|X28=k1_xboole_0|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X28!=k1_xboole_0|v1_funct_2(X28,X26,X27)|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.41  cnf(c_0_33, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_23])).
% 0.13/0.41  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.41  cnf(c_0_35, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.41  cnf(c_0_36, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.41  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.41  fof(c_0_39, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k1_relset_1(X23,X24,X25)=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.41  cnf(c_0_40, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.13/0.41  fof(c_0_42, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.41  cnf(c_0_43, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k2_relat_1(X3),X2)|~v1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.13/0.41  cnf(c_0_44, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.41  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_46, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.41  cnf(c_0_47, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_41])])).
% 0.13/0.41  cnf(c_0_48, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.41  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.41  cnf(c_0_50, negated_conjecture, (k1_xboole_0=esk3_0|k1_xboole_0=esk2_0|r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.13/0.41  cnf(c_0_51, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|k1_xboole_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_38])])).
% 0.13/0.41  fof(c_0_52, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.41  fof(c_0_53, plain, ![X9, X10]:((k4_xboole_0(X9,X10)!=k1_xboole_0|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|k4_xboole_0(X9,X10)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l32_xboole_1])])).
% 0.13/0.41  cnf(c_0_54, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_48])).
% 0.13/0.41  cnf(c_0_55, negated_conjecture, (k1_xboole_0=esk2_0|k1_xboole_0=esk3_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.13/0.41  cnf(c_0_56, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.41  cnf(c_0_57, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.41  cnf(c_0_58, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.41  cnf(c_0_59, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.41  cnf(c_0_60, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_36, c_0_54])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (k1_xboole_0=esk2_0|esk3_0!=esk2_0), inference(ef,[status(thm)],[c_0_55])).
% 0.13/0.41  cnf(c_0_62, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_56])).
% 0.13/0.41  cnf(c_0_63, plain, (k1_xboole_0=X1|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.13/0.41  cnf(c_0_64, plain, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_59]), c_0_60])])).
% 0.13/0.41  fof(c_0_65, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.41  cnf(c_0_66, negated_conjecture, (k2_zfmisc_1(X1,esk3_0)=esk3_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.41  cnf(c_0_67, negated_conjecture, (k4_xboole_0(X1,esk2_0)=X1|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_57, c_0_61])).
% 0.13/0.41  cnf(c_0_68, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_62, c_0_61])).
% 0.13/0.41  cnf(c_0_69, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.13/0.41  cnf(c_0_70, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.41  cnf(c_0_71, negated_conjecture, (k1_xboole_0=esk2_0|esk3_0=X1|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_55])).
% 0.13/0.41  cnf(c_0_72, negated_conjecture, (k1_xboole_0=esk2_0|r1_tarski(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_44, c_0_66])).
% 0.13/0.41  cnf(c_0_73, negated_conjecture, (X1=k1_xboole_0|esk3_0!=esk2_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_67])).
% 0.13/0.41  cnf(c_0_74, negated_conjecture, (r1_tarski(esk4_0,esk2_0)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_44, c_0_68])).
% 0.13/0.41  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk4_0)!=esk2_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_69]), c_0_70]), c_0_45])])).
% 0.13/0.41  cnf(c_0_76, negated_conjecture, (esk3_0=esk4_0|k1_xboole_0=esk2_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.13/0.41  cnf(c_0_77, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.41  cnf(c_0_78, negated_conjecture, (k1_xboole_0=esk4_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.41  cnf(c_0_79, negated_conjecture, (esk2_0=X1|esk3_0!=esk2_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_63, c_0_61])).
% 0.13/0.41  cnf(c_0_80, negated_conjecture, (k1_xboole_0=esk3_0|~r1_tarski(esk4_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_75, c_0_51])).
% 0.13/0.41  cnf(c_0_81, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|esk3_0=esk4_0), inference(spm,[status(thm)],[c_0_62, c_0_76])).
% 0.13/0.41  cnf(c_0_82, negated_conjecture, (k1_relat_1(esk4_0)=esk4_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.41  cnf(c_0_83, negated_conjecture, (r1_tarski(esk4_0,X1)|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_70, c_0_78])).
% 0.13/0.41  cnf(c_0_84, negated_conjecture, (esk2_0=esk4_0|esk3_0!=esk2_0), inference(spm,[status(thm)],[c_0_79, c_0_74])).
% 0.13/0.41  cnf(c_0_85, negated_conjecture, (esk3_0=esk4_0|esk3_0=esk2_0|~r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_80, c_0_76])).
% 0.13/0.41  cnf(c_0_86, negated_conjecture, (esk3_0=esk4_0|r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_44, c_0_81])).
% 0.13/0.41  cnf(c_0_87, negated_conjecture, (esk3_0!=esk2_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_82]), c_0_83]), c_0_84])).
% 0.13/0.41  cnf(c_0_88, negated_conjecture, (esk3_0=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_87])).
% 0.13/0.41  fof(c_0_89, plain, ![X29, X30]:(v1_xboole_0(X29)|~v1_xboole_0(X30)|v1_xboole_0(k1_funct_2(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.13/0.41  fof(c_0_90, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  cnf(c_0_91, negated_conjecture, (k1_xboole_0=esk4_0|k1_xboole_0=esk2_0), inference(rw,[status(thm)],[c_0_55, c_0_88])).
% 0.13/0.41  cnf(c_0_92, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.13/0.41  cnf(c_0_93, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.13/0.41  cnf(c_0_94, negated_conjecture, (k4_xboole_0(X1,esk2_0)=X1|k1_xboole_0=esk4_0), inference(spm,[status(thm)],[c_0_57, c_0_91])).
% 0.13/0.41  cnf(c_0_95, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk4_0))), inference(rw,[status(thm)],[c_0_44, c_0_88])).
% 0.13/0.41  cnf(c_0_96, negated_conjecture, (k2_zfmisc_1(esk2_0,X1)=esk2_0|k1_xboole_0=esk4_0), inference(spm,[status(thm)],[c_0_62, c_0_91])).
% 0.13/0.41  fof(c_0_97, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.41  cnf(c_0_98, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_92, c_0_23])).
% 0.13/0.41  cnf(c_0_99, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.41  cnf(c_0_100, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk3_0,k3_partfun1(k1_xboole_0,esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_93, c_0_31])).
% 0.13/0.41  cnf(c_0_101, negated_conjecture, (k1_xboole_0=esk4_0|X1=k1_xboole_0|~r1_tarski(X1,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_94])).
% 0.13/0.41  cnf(c_0_102, negated_conjecture, (k1_xboole_0=esk4_0|r1_tarski(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 0.13/0.41  cnf(c_0_103, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 0.13/0.41  cnf(c_0_104, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_98, c_0_99])).
% 0.13/0.41  cnf(c_0_105, negated_conjecture, (k1_xboole_0=esk2_0|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_99, c_0_55])).
% 0.13/0.41  cnf(c_0_106, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(k1_xboole_0,esk2_0,esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_88]), c_0_88])).
% 0.13/0.41  cnf(c_0_107, negated_conjecture, (k1_xboole_0=esk4_0), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.13/0.41  cnf(c_0_108, plain, (k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_103, c_0_104])).
% 0.13/0.41  cnf(c_0_109, negated_conjecture, (k1_xboole_0=esk2_0|v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[c_0_105, c_0_88])).
% 0.13/0.41  cnf(c_0_110, negated_conjecture, (esk2_0!=esk4_0), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 0.13/0.41  cnf(c_0_111, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk2_0,esk4_0,k3_partfun1(esk4_0,esk2_0,esk4_0)))), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 0.13/0.41  cnf(c_0_112, plain, (k5_partfun1(X1,esk4_0,k3_partfun1(esk4_0,X1,esk4_0))=esk4_0|v1_xboole_0(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_107]), c_0_107]), c_0_107]), c_0_107])).
% 0.13/0.41  cnf(c_0_113, negated_conjecture, (v1_xboole_0(esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_107]), c_0_110])).
% 0.13/0.41  cnf(c_0_114, plain, (X1=esk4_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_103, c_0_107])).
% 0.13/0.41  cnf(c_0_115, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])])).
% 0.13/0.41  cnf(c_0_116, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_110]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 117
% 0.13/0.41  # Proof object clause steps            : 82
% 0.13/0.41  # Proof object formula steps           : 35
% 0.13/0.41  # Proof object conjectures             : 51
% 0.13/0.41  # Proof object clause conjectures      : 48
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 23
% 0.13/0.41  # Proof object initial formulas used   : 18
% 0.13/0.41  # Proof object generating inferences   : 44
% 0.13/0.41  # Proof object simplifying inferences  : 40
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 18
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 36
% 0.13/0.41  # Removed in clause preprocessing      : 1
% 0.13/0.41  # Initial clauses in saturation        : 35
% 0.13/0.41  # Processed clauses                    : 520
% 0.13/0.41  # ...of these trivial                  : 22
% 0.13/0.41  # ...subsumed                          : 208
% 0.13/0.41  # ...remaining for further processing  : 290
% 0.13/0.41  # Other redundant clauses eliminated   : 12
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 14
% 0.13/0.41  # Backward-rewritten                   : 183
% 0.13/0.41  # Generated clauses                    : 1119
% 0.13/0.41  # ...of the previous two non-trivial   : 1103
% 0.13/0.41  # Contextual simplify-reflections      : 11
% 0.13/0.41  # Paramodulations                      : 1106
% 0.13/0.41  # Factorizations                       : 2
% 0.13/0.41  # Equation resolutions                 : 12
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 52
% 0.13/0.41  #    Positive orientable unit clauses  : 18
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 2
% 0.13/0.41  #    Non-unit-clauses                  : 32
% 0.13/0.41  # Current number of unprocessed clauses: 407
% 0.13/0.41  # ...number of literals in the above   : 1863
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 233
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 4198
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 2124
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 174
% 0.13/0.41  # Unit Clause-clause subsumption calls : 87
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 8
% 0.13/0.41  # BW rewrite match successes           : 7
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 16822
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.057 s
% 0.13/0.41  # System time              : 0.008 s
% 0.13/0.41  # Total time               : 0.065 s
% 0.13/0.41  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
