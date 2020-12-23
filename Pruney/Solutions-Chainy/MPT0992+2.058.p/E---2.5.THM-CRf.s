%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:43 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  132 (1697 expanded)
%              Number of clauses        :   93 ( 719 expanded)
%              Number of leaves         :   19 ( 418 expanded)
%              Depth                    :   25
%              Number of atoms          :  373 (7046 expanded)
%              Number of equality atoms :  100 (2061 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

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
    ! [X41,X42,X43,X44] :
      ( ( v1_funct_1(k2_partfun1(X41,X42,X43,X44))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( m1_subset_1(k2_partfun1(X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
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
    ! [X10] :
      ( ~ r1_tarski(X10,k1_xboole_0)
      | X10 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X13,X14] :
      ( ( ~ m1_subset_1(X13,k1_zfmisc_1(X14))
        | r1_tarski(X13,X14) )
      & ( ~ r1_tarski(X13,X14)
        | m1_subset_1(X13,k1_zfmisc_1(X14)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_30,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_31,plain,(
    ! [X21,X22] : v1_relat_1(k2_zfmisc_1(X21,X22)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_33,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_36])).

fof(c_0_43,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | r1_tarski(k7_relat_1(X26,X25),X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_44,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_38])).

fof(c_0_47,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_48,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_49,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_50,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_52,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k2_partfun1(X45,X46,X47,X48) = k7_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_53,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_46])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_58,plain,(
    ! [X17,X18] :
      ( ( ~ v5_relat_1(X18,X17)
        | r1_tarski(k2_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k2_relat_1(X18),X17)
        | v5_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_59,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_61,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_62,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X40 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != k1_xboole_0
        | v1_funct_2(X40,X38,X39)
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_63,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_28])).

cnf(c_0_64,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_53]),c_0_54])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)
    | esk2_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_51]),c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk2_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_56])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_57])).

fof(c_0_70,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X35)
      | ~ r1_tarski(k2_relat_1(X37),X36)
      | m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_72,negated_conjecture,
    ( v5_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_37])])).

cnf(c_0_74,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_65])]),c_0_66]),c_0_67])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])])).

cnf(c_0_80,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_38]),c_0_77])])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X3))
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_35])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_45]),c_0_25])]),c_0_81])).

fof(c_0_85,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(esk1_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_73]),c_0_84])])).

cnf(c_0_87,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_88,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | v1_relat_1(k7_relat_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_89,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | ~ v4_relat_1(X24,X23)
      | X24 = k7_relat_1(X24,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_90,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_91,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_35])).

cnf(c_0_92,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k7_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_53])).

cnf(c_0_93,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_95,negated_conjecture,
    ( v4_relat_1(esk4_0,X1)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_96,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_53]),c_0_93])).

cnf(c_0_97,negated_conjecture,
    ( k7_relat_1(esk4_0,X1) = esk4_0
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_73])])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_87,c_0_35])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),esk4_0)
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_73])])).

fof(c_0_100,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | ~ r1_tarski(X27,k1_relat_1(X28))
      | k1_relat_1(k7_relat_1(X28,X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_98,c_0_25])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),esk4_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_77])).

cnf(c_0_103,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_105,plain,
    ( k1_relset_1(X1,X2,k7_relat_1(X3,X4)) = X4
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X4,k1_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_74])).

cnf(c_0_106,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_104])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_102])).

cnf(c_0_108,plain,
    ( k1_relset_1(X1,X2,k7_relat_1(X3,X4)) = X4
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_relat_1(X3))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_35])).

cnf(c_0_109,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_69])).

cnf(c_0_110,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_111,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_107]),c_0_73])])).

cnf(c_0_113,negated_conjecture,
    ( k1_relset_1(X1,X2,k7_relat_1(esk4_0,X3)) = X3
    | ~ m1_subset_1(k7_relat_1(esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_84]),c_0_73])])).

cnf(c_0_114,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(k7_relat_1(X1,X2)))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_103]),c_0_93])).

cnf(c_0_115,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_64])).

cnf(c_0_116,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relat_1(X2) != X3
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_74])).

cnf(c_0_117,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_111]),c_0_112])])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | ~ m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( m1_subset_1(k7_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(k7_relat_1(X1,esk3_0)))))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(esk3_0,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_27])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_27])).

cnf(c_0_121,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(X1,X2,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_115]),c_0_24]),c_0_25])])).

cnf(c_0_122,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(X2,X3),X3,X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(X3,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_103])])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_117]),c_0_112])])).

cnf(c_0_124,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk3_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_119]),c_0_120]),c_0_73]),c_0_84]),c_0_27])])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_64]),c_0_24])])).

cnf(c_0_126,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(esk4_0,X2),X2,X1)
    | ~ m1_subset_1(k7_relat_1(esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ r1_tarski(X2,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_84]),c_0_73])])).

cnf(c_0_127,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_128,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_27])]),c_0_81])).

cnf(c_0_129,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_127,c_0_69])).

cnf(c_0_130,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_131,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_25,c_0_130]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:22:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 4.12/4.30  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 4.12/4.30  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.12/4.30  #
% 4.12/4.30  # Preprocessing time       : 0.028 s
% 4.12/4.30  # Presaturation interreduction done
% 4.12/4.30  
% 4.12/4.30  # Proof found!
% 4.12/4.30  # SZS status Theorem
% 4.12/4.30  # SZS output start CNFRefutation
% 4.12/4.30  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 4.12/4.30  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.12/4.30  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.12/4.30  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.12/4.30  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.12/4.30  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.12/4.30  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 4.12/4.30  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.12/4.30  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.12/4.30  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.12/4.30  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.12/4.30  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.12/4.30  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.12/4.30  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.12/4.30  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.12/4.30  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.12/4.30  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.12/4.30  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.12/4.30  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.12/4.30  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 4.12/4.30  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk3_0,esk1_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 4.12/4.30  fof(c_0_21, plain, ![X41, X42, X43, X44]:((v1_funct_1(k2_partfun1(X41,X42,X43,X44))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(m1_subset_1(k2_partfun1(X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|(~v1_funct_1(X43)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 4.12/4.30  cnf(c_0_22, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.12/4.30  cnf(c_0_23, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.12/4.30  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.12/4.30  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.12/4.30  fof(c_0_26, plain, ![X10]:(~r1_tarski(X10,k1_xboole_0)|X10=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 4.12/4.30  cnf(c_0_27, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.12/4.30  cnf(c_0_28, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.12/4.30  fof(c_0_29, plain, ![X13, X14]:((~m1_subset_1(X13,k1_zfmisc_1(X14))|r1_tarski(X13,X14))&(~r1_tarski(X13,X14)|m1_subset_1(X13,k1_zfmisc_1(X14)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 4.12/4.30  fof(c_0_30, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 4.12/4.30  fof(c_0_31, plain, ![X21, X22]:v1_relat_1(k2_zfmisc_1(X21,X22)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 4.12/4.30  cnf(c_0_32, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])])).
% 4.12/4.30  cnf(c_0_33, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.12/4.30  cnf(c_0_34, negated_conjecture, (r1_tarski(esk3_0,k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 4.12/4.30  cnf(c_0_35, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.12/4.30  cnf(c_0_36, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 4.12/4.30  cnf(c_0_37, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 4.12/4.30  cnf(c_0_38, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_30])).
% 4.12/4.30  cnf(c_0_39, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_32, c_0_28])).
% 4.12/4.30  cnf(c_0_40, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 4.12/4.30  cnf(c_0_41, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_33, c_0_35])).
% 4.12/4.30  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_36])).
% 4.12/4.30  fof(c_0_43, plain, ![X25, X26]:(~v1_relat_1(X26)|r1_tarski(k7_relat_1(X26,X25),X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 4.12/4.30  cnf(c_0_44, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 4.12/4.30  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.12/4.30  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_38])).
% 4.12/4.30  fof(c_0_47, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 4.12/4.30  fof(c_0_48, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 4.12/4.30  fof(c_0_49, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 4.12/4.30  cnf(c_0_50, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 4.12/4.30  cnf(c_0_51, negated_conjecture, (esk4_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 4.12/4.30  fof(c_0_52, plain, ![X45, X46, X47, X48]:(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k2_partfun1(X45,X46,X47,X48)=k7_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 4.12/4.30  cnf(c_0_53, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 4.12/4.30  cnf(c_0_54, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_44])).
% 4.12/4.30  cnf(c_0_55, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_28])).
% 4.12/4.30  cnf(c_0_56, negated_conjecture, (esk4_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_46])).
% 4.12/4.30  cnf(c_0_57, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_47])).
% 4.12/4.30  fof(c_0_58, plain, ![X17, X18]:((~v5_relat_1(X18,X17)|r1_tarski(k2_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k2_relat_1(X18),X17)|v5_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 4.12/4.30  cnf(c_0_59, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.12/4.30  cnf(c_0_60, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 4.12/4.30  fof(c_0_61, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 4.12/4.30  fof(c_0_62, plain, ![X38, X39, X40]:((((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))))&((~v1_funct_2(X40,X38,X39)|X40=k1_xboole_0|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X40!=k1_xboole_0|v1_funct_2(X40,X38,X39)|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 4.12/4.30  cnf(c_0_63, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k2_partfun1(k1_xboole_0,esk2_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_28])).
% 4.12/4.30  cnf(c_0_64, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 4.12/4.30  cnf(c_0_65, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_53]), c_0_54])])).
% 4.12/4.30  cnf(c_0_66, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk2_0)|esk2_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_51]), c_0_28])).
% 4.12/4.30  cnf(c_0_67, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk2_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_56])).
% 4.12/4.30  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 4.12/4.30  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_57])).
% 4.12/4.30  fof(c_0_70, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k1_relat_1(X37),X35)|~r1_tarski(k2_relat_1(X37),X36)|m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 4.12/4.30  cnf(c_0_71, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 4.12/4.30  cnf(c_0_72, negated_conjecture, (v5_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_25])).
% 4.12/4.30  cnf(c_0_73, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_25]), c_0_37])])).
% 4.12/4.30  cnf(c_0_74, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 4.12/4.30  cnf(c_0_75, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 4.12/4.30  cnf(c_0_76, negated_conjecture, (esk2_0!=k1_xboole_0|~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_65])]), c_0_66]), c_0_67])).
% 4.12/4.30  cnf(c_0_77, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 4.12/4.30  cnf(c_0_78, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 4.12/4.30  cnf(c_0_79, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])])).
% 4.12/4.30  cnf(c_0_80, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 4.12/4.30  cnf(c_0_81, negated_conjecture, (esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_38]), c_0_77])])).
% 4.12/4.30  cnf(c_0_82, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X3))|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_78, c_0_35])).
% 4.12/4.30  cnf(c_0_83, negated_conjecture, (m1_subset_1(k2_relat_1(esk4_0),k1_zfmisc_1(esk2_0))), inference(spm,[status(thm)],[c_0_68, c_0_79])).
% 4.12/4.30  cnf(c_0_84, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_45]), c_0_25])]), c_0_81])).
% 4.12/4.30  fof(c_0_85, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 4.12/4.30  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~r1_tarski(esk1_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_73]), c_0_84])])).
% 4.12/4.30  cnf(c_0_87, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 4.12/4.30  fof(c_0_88, plain, ![X19, X20]:(~v1_relat_1(X19)|v1_relat_1(k7_relat_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 4.12/4.30  fof(c_0_89, plain, ![X23, X24]:(~v1_relat_1(X24)|~v4_relat_1(X24,X23)|X24=k7_relat_1(X24,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 4.12/4.30  cnf(c_0_90, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 4.12/4.30  cnf(c_0_91, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_86, c_0_35])).
% 4.12/4.30  cnf(c_0_92, plain, (r1_tarski(X1,X2)|~v1_relat_1(X2)|~r1_tarski(X1,k7_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_87, c_0_53])).
% 4.12/4.30  cnf(c_0_93, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_88])).
% 4.12/4.30  cnf(c_0_94, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 4.12/4.30  cnf(c_0_95, negated_conjecture, (v4_relat_1(esk4_0,X1)|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 4.12/4.30  cnf(c_0_96, plain, (r1_tarski(k7_relat_1(k7_relat_1(X1,X2),X3),X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_53]), c_0_93])).
% 4.12/4.30  cnf(c_0_97, negated_conjecture, (k7_relat_1(esk4_0,X1)=esk4_0|~m1_subset_1(esk1_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_73])])).
% 4.12/4.30  cnf(c_0_98, plain, (r1_tarski(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_87, c_0_35])).
% 4.12/4.30  cnf(c_0_99, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),esk4_0)|~m1_subset_1(esk1_0,k1_zfmisc_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_73])])).
% 4.12/4.30  fof(c_0_100, plain, ![X27, X28]:(~v1_relat_1(X28)|(~r1_tarski(X27,k1_relat_1(X28))|k1_relat_1(k7_relat_1(X28,X27))=X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 4.12/4.30  cnf(c_0_101, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk1_0,esk2_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_98, c_0_25])).
% 4.12/4.30  cnf(c_0_102, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),esk4_0)), inference(spm,[status(thm)],[c_0_99, c_0_77])).
% 4.12/4.30  cnf(c_0_103, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_100])).
% 4.12/4.30  cnf(c_0_104, negated_conjecture, (r1_tarski(k7_relat_1(esk4_0,X1),k2_zfmisc_1(esk1_0,esk2_0))), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 4.12/4.30  cnf(c_0_105, plain, (k1_relset_1(X1,X2,k7_relat_1(X3,X4))=X4|~v1_relat_1(X3)|~m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(X4,k1_relat_1(X3))), inference(spm,[status(thm)],[c_0_103, c_0_74])).
% 4.12/4.30  cnf(c_0_106, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(spm,[status(thm)],[c_0_68, c_0_104])).
% 4.12/4.30  cnf(c_0_107, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(esk4_0))), inference(spm,[status(thm)],[c_0_68, c_0_102])).
% 4.12/4.30  cnf(c_0_108, plain, (k1_relset_1(X1,X2,k7_relat_1(X3,X4))=X4|~v1_relat_1(X3)|~m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,k1_zfmisc_1(k1_relat_1(X3)))), inference(spm,[status(thm)],[c_0_105, c_0_35])).
% 4.12/4.30  cnf(c_0_109, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X1))))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_78, c_0_69])).
% 4.12/4.30  cnf(c_0_110, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 4.12/4.30  cnf(c_0_111, negated_conjecture, (v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_59, c_0_106])).
% 4.12/4.30  cnf(c_0_112, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_107]), c_0_73])])).
% 4.12/4.30  cnf(c_0_113, negated_conjecture, (k1_relset_1(X1,X2,k7_relat_1(esk4_0,X3))=X3|~m1_subset_1(k7_relat_1(esk4_0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_84]), c_0_73])])).
% 4.12/4.30  cnf(c_0_114, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,k2_relat_1(k7_relat_1(X1,X2)))))|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~r1_tarski(X2,X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_103]), c_0_93])).
% 4.12/4.30  cnf(c_0_115, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_64, c_0_64])).
% 4.12/4.30  cnf(c_0_116, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relat_1(X2)!=X3|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(spm,[status(thm)],[c_0_110, c_0_74])).
% 4.12/4.30  cnf(c_0_117, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_111]), c_0_112])])).
% 4.12/4.30  cnf(c_0_118, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|~m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_74, c_0_113])).
% 4.12/4.30  cnf(c_0_119, negated_conjecture, (m1_subset_1(k7_relat_1(X1,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk1_0,k2_relat_1(k7_relat_1(X1,esk3_0)))))|~v1_relat_1(X1)|~r1_tarski(esk3_0,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_114, c_0_27])).
% 4.12/4.30  cnf(c_0_120, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_68, c_0_27])).
% 4.12/4.30  cnf(c_0_121, negated_conjecture, (~v1_funct_2(k2_partfun1(X1,X2,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(X1,X2,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_115]), c_0_24]), c_0_25])])).
% 4.12/4.30  cnf(c_0_122, plain, (X1=k1_xboole_0|v1_funct_2(k7_relat_1(X2,X3),X3,X1)|~v1_relat_1(X2)|~m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(X3,k1_relat_1(X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_103])])).
% 4.12/4.30  cnf(c_0_123, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,esk2_0)))|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,X1)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_117]), c_0_112])])).
% 4.12/4.30  cnf(c_0_124, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk3_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_119]), c_0_120]), c_0_73]), c_0_84]), c_0_27])])).
% 4.12/4.30  cnf(c_0_125, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_64]), c_0_24])])).
% 4.12/4.30  cnf(c_0_126, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(k7_relat_1(esk4_0,X2),X2,X1)|~m1_subset_1(k7_relat_1(esk4_0,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~r1_tarski(X2,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_84]), c_0_73])])).
% 4.12/4.30  cnf(c_0_127, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_123, c_0_124])).
% 4.12/4.30  cnf(c_0_128, negated_conjecture, (~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_27])]), c_0_81])).
% 4.12/4.30  cnf(c_0_129, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_127, c_0_69])).
% 4.12/4.30  cnf(c_0_130, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 4.12/4.30  cnf(c_0_131, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_25, c_0_130]), ['proof']).
% 4.12/4.30  # SZS output end CNFRefutation
% 4.12/4.30  # Proof object total steps             : 132
% 4.12/4.30  # Proof object clause steps            : 93
% 4.12/4.30  # Proof object formula steps           : 39
% 4.12/4.30  # Proof object conjectures             : 56
% 4.12/4.30  # Proof object clause conjectures      : 53
% 4.12/4.30  # Proof object formula conjectures     : 3
% 4.12/4.30  # Proof object initial clauses used    : 28
% 4.12/4.30  # Proof object initial formulas used   : 19
% 4.12/4.30  # Proof object generating inferences   : 62
% 4.12/4.30  # Proof object simplifying inferences  : 58
% 4.12/4.30  # Training examples: 0 positive, 0 negative
% 4.12/4.30  # Parsed axioms                        : 19
% 4.12/4.30  # Removed by relevancy pruning/SinE    : 0
% 4.12/4.30  # Initial clauses                      : 37
% 4.12/4.30  # Removed in clause preprocessing      : 0
% 4.12/4.30  # Initial clauses in saturation        : 37
% 4.12/4.30  # Processed clauses                    : 48692
% 4.12/4.30  # ...of these trivial                  : 378
% 4.12/4.30  # ...subsumed                          : 44269
% 4.12/4.30  # ...remaining for further processing  : 4045
% 4.12/4.30  # Other redundant clauses eliminated   : 574
% 4.12/4.30  # Clauses deleted for lack of memory   : 0
% 4.12/4.30  # Backward-subsumed                    : 740
% 4.12/4.30  # Backward-rewritten                   : 189
% 4.12/4.30  # Generated clauses                    : 270766
% 4.12/4.30  # ...of the previous two non-trivial   : 231359
% 4.12/4.30  # Contextual simplify-reflections      : 518
% 4.12/4.30  # Paramodulations                      : 270144
% 4.12/4.30  # Factorizations                       : 0
% 4.12/4.30  # Equation resolutions                 : 620
% 4.12/4.30  # Propositional unsat checks           : 0
% 4.12/4.30  #    Propositional check models        : 0
% 4.12/4.30  #    Propositional check unsatisfiable : 0
% 4.12/4.30  #    Propositional clauses             : 0
% 4.12/4.30  #    Propositional clauses after purity: 0
% 4.12/4.30  #    Propositional unsat core size     : 0
% 4.12/4.30  #    Propositional preprocessing time  : 0.000
% 4.12/4.30  #    Propositional encoding time       : 0.000
% 4.12/4.30  #    Propositional solver time         : 0.000
% 4.12/4.30  #    Success case prop preproc time    : 0.000
% 4.12/4.30  #    Success case prop encoding time   : 0.000
% 4.12/4.30  #    Success case prop solver time     : 0.000
% 4.12/4.30  # Current number of processed clauses  : 3076
% 4.12/4.30  #    Positive orientable unit clauses  : 170
% 4.12/4.30  #    Positive unorientable unit clauses: 0
% 4.12/4.30  #    Negative unit clauses             : 38
% 4.12/4.30  #    Non-unit-clauses                  : 2868
% 4.12/4.30  # Current number of unprocessed clauses: 179905
% 4.12/4.30  # ...number of literals in the above   : 1092867
% 4.12/4.30  # Current number of archived formulas  : 0
% 4.12/4.30  # Current number of archived clauses   : 967
% 4.12/4.30  # Clause-clause subsumption calls (NU) : 2631255
% 4.12/4.30  # Rec. Clause-clause subsumption calls : 533667
% 4.12/4.30  # Non-unit clause-clause subsumptions  : 14176
% 4.12/4.30  # Unit Clause-clause subsumption calls : 17187
% 4.12/4.30  # Rewrite failures with RHS unbound    : 0
% 4.12/4.30  # BW rewrite match attempts            : 672
% 4.12/4.30  # BW rewrite match successes           : 77
% 4.12/4.30  # Condensation attempts                : 0
% 4.12/4.30  # Condensation successes               : 0
% 4.12/4.30  # Termbank termtop insertions          : 6849695
% 4.12/4.31  
% 4.12/4.31  # -------------------------------------------------
% 4.12/4.31  # User time                : 3.859 s
% 4.12/4.31  # System time              : 0.105 s
% 4.12/4.31  # Total time               : 3.964 s
% 4.12/4.31  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
