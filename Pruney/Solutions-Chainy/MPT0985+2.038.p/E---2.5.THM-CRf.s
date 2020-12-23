%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  103 (3223 expanded)
%              Number of clauses        :   75 (1248 expanded)
%              Number of leaves         :   14 ( 801 expanded)
%              Depth                    :   18
%              Number of atoms          :  329 (15624 expanded)
%              Number of equality atoms :   84 (2764 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(rc2_subset_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
      & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

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

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X37] :
      ( ( v1_funct_1(X37)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_2(X37,k1_relat_1(X37),k2_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X37),k2_relat_1(X37))))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_16,plain,(
    ! [X12] :
      ( ( k2_relat_1(X12) = k1_relat_1(k2_funct_1(X12))
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) )
      & ( k1_relat_1(X12) = k2_relat_1(k2_funct_1(X12))
        | ~ v2_funct_1(X12)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) = k2_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v2_funct_1(esk5_0)
    & k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0
    & ( ~ v1_funct_1(k2_funct_1(esk5_0))
      | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | X5 = X6
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_30,plain,(
    ! [X9] :
      ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(X9))
      & v1_xboole_0(esk2_1(X9)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(pm,[status(thm)],[c_0_26,c_0_24])).

fof(c_0_36,plain,(
    ! [X34,X35,X36] :
      ( ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X35 = k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X34 = k1_relset_1(X34,X35,X36)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X34 != k1_relset_1(X34,X35,X36)
        | v1_funct_2(X36,X34,X35)
        | X34 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( ~ v1_funct_2(X36,X34,X35)
        | X36 = k1_xboole_0
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( X36 != k1_xboole_0
        | v1_funct_2(X36,X34,X35)
        | X34 = k1_xboole_0
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( k1_xboole_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_40,plain,
    ( v1_xboole_0(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)))))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(pm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,plain,
    ( esk2_1(X1) = k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0))))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_42]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_24]),c_0_44]),c_0_45])])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46,c_0_32]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_48])).

fof(c_0_53,plain,(
    ! [X28,X29,X30] :
      ( ( v1_funct_1(X30)
        | ~ v1_funct_1(X30)
        | ~ v1_partfun1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( v1_funct_2(X30,X28,X29)
        | ~ v1_funct_1(X30)
        | ~ v1_partfun1(X30,X28)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

fof(c_0_54,plain,(
    ! [X16,X17,X18] :
      ( ~ v1_xboole_0(X16)
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | v1_xboole_0(X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(pm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_42]),c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_58,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_37,c_0_52])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_60,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_xboole_0(X31)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | v1_partfun1(X33,X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_61,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21,c_0_32]),c_0_34]),c_0_35])])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_relat_1(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38,c_0_32]),c_0_34]),c_0_35])])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(pm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(pm,[status(thm)],[c_0_57,c_0_50])).

fof(c_0_67,plain,(
    ! [X11] :
      ( ( v1_relat_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( v1_funct_1(k2_funct_1(X11))
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ v1_xboole_0(k2_funct_1(esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_55,c_0_28])).

cnf(c_0_69,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_52]),c_0_58])).

cnf(c_0_70,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_59,c_0_52])).

cnf(c_0_71,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(k1_relat_1(esk5_0)) ),
    inference(pm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | esk5_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_63,c_0_62]),c_0_64])])).

cnf(c_0_74,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(pm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_75,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_xboole_0(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68,c_0_52]),c_0_29])])).

cnf(c_0_77,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_78,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_partfun1(k1_xboole_0,X1)
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( v1_partfun1(k1_xboole_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_71,c_0_52])).

cnf(c_0_80,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_xboole_0(esk5_0)
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_73]),c_0_29])])).

cnf(c_0_81,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74,c_0_75]),c_0_34]),c_0_35])])).

cnf(c_0_82,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_83,negated_conjecture,
    ( ~ v1_funct_2(X1,esk4_0,esk3_0)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_xboole_0(k2_funct_1(esk5_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_76,c_0_28])).

cnf(c_0_84,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | k1_relat_1(k1_xboole_0) != X1
    | X1 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_52]),c_0_58])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_39,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_82]),c_0_34]),c_0_35])])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != esk4_0
    | esk4_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_xboole_0(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_84]),c_0_29])])).

cnf(c_0_89,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_85]),c_0_48]),c_0_29])])).

cnf(c_0_90,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_91,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != esk4_0
    | esk4_0 != k1_xboole_0
    | ~ v1_xboole_0(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88,c_0_82]),c_0_34]),c_0_35])])).

cnf(c_0_92,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(ef,[status(thm)],[c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_87]),c_0_87])]),c_0_90])).

cnf(c_0_95,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_87]),c_0_90]),c_0_90]),c_0_90]),c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_98,plain,
    ( v1_relat_1(esk2_1(k2_zfmisc_1(X1,X2))) ),
    inference(pm,[status(thm)],[c_0_26,c_0_47])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61,c_0_96]),c_0_29])]),c_0_97])).

cnf(c_0_100,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_98,c_0_48])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99,c_0_75]),c_0_93]),c_0_100])])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_101,c_0_82]),c_0_93]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.20/0.49  # and selection function NoSelection.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.028 s
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.49  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.49  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.49  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.49  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.20/0.49  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.49  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.49  fof(rc2_subset_1, axiom, ![X1]:?[X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))&v1_xboole_0(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 0.20/0.49  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.49  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.20/0.49  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.20/0.49  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.20/0.49  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.49  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.20/0.49  fof(c_0_15, plain, ![X37]:(((v1_funct_1(X37)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(v1_funct_2(X37,k1_relat_1(X37),k2_relat_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X37),k2_relat_1(X37))))|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.49  fof(c_0_16, plain, ![X12]:((k2_relat_1(X12)=k1_relat_1(k2_funct_1(X12))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))&(k1_relat_1(X12)=k2_relat_1(k2_funct_1(X12))|~v2_funct_1(X12)|(~v1_relat_1(X12)|~v1_funct_1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.49  fof(c_0_17, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_relset_1(X25,X26,X27)=k2_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.49  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v2_funct_1(esk5_0)&k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0)&(~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.49  fof(c_0_19, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.49  fof(c_0_20, plain, ![X5, X6]:(~v1_xboole_0(X5)|X5=X6|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.20/0.49  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_22, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_23, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.49  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_25, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.49  fof(c_0_27, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.49  cnf(c_0_28, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.49  cnf(c_0_29, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.49  fof(c_0_30, plain, ![X9]:(m1_subset_1(esk2_1(X9),k1_zfmisc_1(X9))&v1_xboole_0(esk2_1(X9))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_subset_1])])).
% 0.20/0.49  cnf(c_0_31, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.49  cnf(c_0_32, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.20/0.49  cnf(c_0_33, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk5_0)), inference(pm,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.49  fof(c_0_36, plain, ![X34, X35, X36]:((((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X35=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))&((~v1_funct_2(X36,X34,X35)|X34=k1_relset_1(X34,X35,X36)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X34!=k1_relset_1(X34,X35,X36)|v1_funct_2(X36,X34,X35)|X34!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))))&((~v1_funct_2(X36,X34,X35)|X36=k1_xboole_0|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35))))&(X36!=k1_xboole_0|v1_funct_2(X36,X34,X35)|X34=k1_xboole_0|X35!=k1_xboole_0|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.49  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.49  cnf(c_0_38, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.49  cnf(c_0_39, plain, (k1_xboole_0=X1|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.49  cnf(c_0_40, plain, (v1_xboole_0(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.49  cnf(c_0_41, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)))))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_42, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.49  cnf(c_0_43, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_44, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(pm,[status(thm)],[c_0_37, c_0_24])).
% 0.20/0.49  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_46, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_38, c_0_22])).
% 0.20/0.49  cnf(c_0_47, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.49  cnf(c_0_48, plain, (esk2_1(X1)=k1_xboole_0), inference(pm,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.49  cnf(c_0_49, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0))))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_42]), c_0_33]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_24]), c_0_44]), c_0_45])])).
% 0.20/0.49  cnf(c_0_51, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0)))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_46, c_0_32]), c_0_33]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_52, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.49  fof(c_0_53, plain, ![X28, X29, X30]:((v1_funct_1(X30)|(~v1_funct_1(X30)|~v1_partfun1(X30,X28))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(v1_funct_2(X30,X28,X29)|(~v1_funct_1(X30)|~v1_partfun1(X30,X28))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.20/0.49  fof(c_0_54, plain, ![X16, X17, X18]:(~v1_xboole_0(X16)|(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|v1_xboole_0(X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.20/0.49  cnf(c_0_55, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.49  cnf(c_0_56, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(pm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.49  cnf(c_0_57, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0))|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_42]), c_0_33]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_58, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_37, c_0_52])).
% 0.20/0.49  cnf(c_0_59, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.20/0.49  fof(c_0_60, plain, ![X31, X32, X33]:(~v1_xboole_0(X31)|(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|v1_partfun1(X33,X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.20/0.49  cnf(c_0_61, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.49  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21, c_0_32]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_63, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk5_0,k1_relat_1(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38, c_0_32]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(pm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.49  cnf(c_0_66, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(pm,[status(thm)],[c_0_57, c_0_50])).
% 0.20/0.49  fof(c_0_67, plain, ![X11]:((v1_relat_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(v1_funct_1(k2_funct_1(X11))|(~v1_relat_1(X11)|~v1_funct_1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.49  cnf(c_0_68, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_funct_1(k2_funct_1(esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))|~v1_xboole_0(k2_funct_1(esk5_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_55, c_0_28])).
% 0.20/0.49  cnf(c_0_69, plain, (k1_relat_1(k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_52]), c_0_58])).
% 0.20/0.49  cnf(c_0_70, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)|~v1_funct_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_59, c_0_52])).
% 0.20/0.49  cnf(c_0_71, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.49  cnf(c_0_72, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(k1_relat_1(esk5_0))), inference(pm,[status(thm)],[c_0_61, c_0_62])).
% 0.20/0.49  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|esk5_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_63, c_0_62]), c_0_64])])).
% 0.20/0.49  cnf(c_0_74, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_1(k2_funct_1(esk5_0))|~v1_relat_1(k2_funct_1(esk5_0))), inference(pm,[status(thm)],[c_0_65, c_0_66])).
% 0.20/0.49  cnf(c_0_75, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.49  cnf(c_0_76, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_funct_1(k2_funct_1(esk5_0))|~v1_xboole_0(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_68, c_0_52]), c_0_29])])).
% 0.20/0.49  cnf(c_0_77, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.49  cnf(c_0_78, plain, (k1_relat_1(k1_xboole_0)=X1|X2=k1_xboole_0|~v1_partfun1(k1_xboole_0,X1)|~v1_funct_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.49  cnf(c_0_79, plain, (v1_partfun1(k1_xboole_0,X1)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_71, c_0_52])).
% 0.20/0.49  cnf(c_0_80, negated_conjecture, (esk5_0=k1_xboole_0|v1_xboole_0(esk5_0)|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_73]), c_0_29])])).
% 0.20/0.49  cnf(c_0_81, negated_conjecture, (esk4_0=k1_xboole_0|~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74, c_0_75]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_82, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.49  cnf(c_0_83, negated_conjecture, (~v1_funct_2(X1,esk4_0,esk3_0)|~v1_funct_1(k2_funct_1(esk5_0))|~v1_xboole_0(k2_funct_1(esk5_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_76, c_0_28])).
% 0.20/0.49  cnf(c_0_84, plain, (v1_funct_2(k1_xboole_0,X1,X2)|k1_relat_1(k1_xboole_0)!=X1|X1!=k1_xboole_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_52]), c_0_58])).
% 0.20/0.49  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.49  cnf(c_0_86, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_39, c_0_80])).
% 0.20/0.49  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_82]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_88, negated_conjecture, (k1_relat_1(k1_xboole_0)!=esk4_0|esk4_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk5_0))|~v1_xboole_0(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_84]), c_0_29])])).
% 0.20/0.49  cnf(c_0_89, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|X1=k1_xboole_0|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_85]), c_0_48]), c_0_29])])).
% 0.20/0.49  cnf(c_0_90, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_87])])).
% 0.20/0.49  cnf(c_0_91, negated_conjecture, (k1_relat_1(k1_xboole_0)!=esk4_0|esk4_0!=k1_xboole_0|~v1_xboole_0(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_88, c_0_82]), c_0_34]), c_0_35])])).
% 0.20/0.49  cnf(c_0_92, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~v1_funct_1(k1_xboole_0)), inference(ef,[status(thm)],[c_0_89])).
% 0.20/0.49  cnf(c_0_93, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_34, c_0_90])).
% 0.20/0.49  cnf(c_0_94, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0|~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_87]), c_0_87])]), c_0_90])).
% 0.20/0.49  cnf(c_0_95, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 0.20/0.49  cnf(c_0_96, negated_conjecture, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(k1_xboole_0)))))|~v1_funct_1(k2_funct_1(k1_xboole_0))|~v1_relat_1(k2_funct_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_87]), c_0_90]), c_0_90]), c_0_90]), c_0_90])).
% 0.20/0.49  cnf(c_0_97, negated_conjecture, (~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.20/0.49  cnf(c_0_98, plain, (v1_relat_1(esk2_1(k2_zfmisc_1(X1,X2)))), inference(pm,[status(thm)],[c_0_26, c_0_47])).
% 0.20/0.49  cnf(c_0_99, negated_conjecture, (~v1_funct_1(k2_funct_1(k1_xboole_0))|~v1_relat_1(k2_funct_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_61, c_0_96]), c_0_29])]), c_0_97])).
% 0.20/0.49  cnf(c_0_100, plain, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_98, c_0_48])).
% 0.20/0.49  cnf(c_0_101, negated_conjecture, (~v1_funct_1(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_99, c_0_75]), c_0_93]), c_0_100])])).
% 0.20/0.49  cnf(c_0_102, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_101, c_0_82]), c_0_93]), c_0_100])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 103
% 0.20/0.49  # Proof object clause steps            : 75
% 0.20/0.49  # Proof object formula steps           : 28
% 0.20/0.49  # Proof object conjectures             : 42
% 0.20/0.49  # Proof object clause conjectures      : 39
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 25
% 0.20/0.49  # Proof object initial formulas used   : 14
% 0.20/0.49  # Proof object generating inferences   : 42
% 0.20/0.49  # Proof object simplifying inferences  : 75
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 17
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 35
% 0.20/0.49  # Removed in clause preprocessing      : 2
% 0.20/0.49  # Initial clauses in saturation        : 33
% 0.20/0.49  # Processed clauses                    : 822
% 0.20/0.49  # ...of these trivial                  : 14
% 0.20/0.49  # ...subsumed                          : 453
% 0.20/0.49  # ...remaining for further processing  : 355
% 0.20/0.49  # Other redundant clauses eliminated   : 0
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 82
% 0.20/0.49  # Backward-rewritten                   : 194
% 0.20/0.49  # Generated clauses                    : 5944
% 0.20/0.49  # ...of the previous two non-trivial   : 5555
% 0.20/0.49  # Contextual simplify-reflections      : 0
% 0.20/0.49  # Paramodulations                      : 5918
% 0.20/0.49  # Factorizations                       : 23
% 0.20/0.49  # Equation resolutions                 : 3
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 79
% 0.20/0.49  #    Positive orientable unit clauses  : 16
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 3
% 0.20/0.49  #    Non-unit-clauses                  : 60
% 0.20/0.49  # Current number of unprocessed clauses: 4523
% 0.20/0.49  # ...number of literals in the above   : 28980
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 276
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 4831
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 2631
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 513
% 0.20/0.49  # Unit Clause-clause subsumption calls : 203
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 21
% 0.20/0.49  # BW rewrite match successes           : 10
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 37324
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.137 s
% 0.20/0.49  # System time              : 0.008 s
% 0.20/0.49  # Total time               : 0.146 s
% 0.20/0.49  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
