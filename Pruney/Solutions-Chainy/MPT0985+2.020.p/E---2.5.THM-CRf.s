%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:35 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 (1618 expanded)
%              Number of clauses        :   67 ( 640 expanded)
%              Number of leaves         :   19 ( 414 expanded)
%              Depth                    :   16
%              Number of atoms          :  286 (7348 expanded)
%              Number of equality atoms :   80 (1558 expanded)
%              Maximal formula depth    :   14 (   3 average)
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_22,plain,(
    ! [X42] :
      ( ( v1_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( v1_funct_2(X42,k1_relat_1(X42),k2_relat_1(X42))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X42),k2_relat_1(X42))))
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_23,plain,(
    ! [X24] :
      ( ( k2_relat_1(X24) = k1_relat_1(k2_funct_1(X24))
        | ~ v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) )
      & ( k1_relat_1(X24) = k2_relat_1(k2_funct_1(X24))
        | ~ v2_funct_1(X24)
        | ~ v1_relat_1(X24)
        | ~ v1_funct_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_24,plain,(
    ! [X21] :
      ( ( v1_relat_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_25,plain,(
    ! [X37,X38,X39] :
      ( ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X38 = k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X37 = k1_relset_1(X37,X38,X39)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_relset_1(X37,X38,X39)
        | v1_funct_2(X39,X37,X38)
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ v1_funct_2(X39,X37,X38)
        | X39 = k1_xboole_0
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X39 != k1_xboole_0
        | v1_funct_2(X39,X37,X38)
        | X37 = k1_xboole_0
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_26,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_28,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | v1_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_29,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_38,plain,(
    ! [X40] :
      ( v1_partfun1(k6_partfun1(X40),X40)
      & m1_subset_1(k6_partfun1(X40),k1_zfmisc_1(k2_zfmisc_1(X40,X40))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_39,plain,(
    ! [X41] : k6_partfun1(X41) = k6_relat_1(X41) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_40,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_47,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_relat_1(esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_42])])).

cnf(c_0_54,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_42]),c_0_46])])).

cnf(c_0_55,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_27]),c_0_48])).

fof(c_0_57,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | X5 = X6
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_58,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_xboole_0(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_59,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_46])])).

cnf(c_0_63,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_45]),c_0_42]),c_0_46])])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_67,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_56]),c_0_42]),c_0_46])])).

cnf(c_0_69,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_44]),c_0_45]),c_0_42]),c_0_46])])).

cnf(c_0_70,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_72,plain,(
    ! [X19] :
      ( k1_relat_1(k6_relat_1(X19)) = X19
      & k2_relat_1(k6_relat_1(X19)) = X19 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_64]),c_0_60]),c_0_65])])).

cnf(c_0_74,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_65])])).

fof(c_0_75,plain,(
    ! [X20] :
      ( ~ v1_xboole_0(X20)
      | v1_funct_1(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

fof(c_0_76,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_55]),c_0_56]),c_0_45]),c_0_42]),c_0_46])]),c_0_70])).

cnf(c_0_79,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_65])])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_65])).

cnf(c_0_87,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_60])).

cnf(c_0_88,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_78]),c_0_78]),c_0_60])).

cnf(c_0_90,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_85]),c_0_79]),c_0_86]),c_0_87])])).

cnf(c_0_91,negated_conjecture,
    ( v2_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_88]),c_0_88])).

cnf(c_0_93,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

fof(c_0_94,plain,(
    ! [X43,X44] :
      ( ( v1_funct_1(X44)
        | ~ r1_tarski(k2_relat_1(X44),X43)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( v1_funct_2(X44,k1_relat_1(X44),X43)
        | ~ r1_tarski(k2_relat_1(X44),X43)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),X43)))
        | ~ r1_tarski(k2_relat_1(X44),X43)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_95,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_96,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])])).

cnf(c_0_98,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_93]),c_0_65])])).

cnf(c_0_99,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_100,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_81])).

cnf(c_0_101,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_2(X1,k1_xboole_0,esk1_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_64]),c_0_98])])).

cnf(c_0_103,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_86]),c_0_87]),c_0_101])]),c_0_85])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_65])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:51:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.20/0.48  # and selection function SelectNewComplexAHPNS.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.046 s
% 0.20/0.48  # Presaturation interreduction done
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.48  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.48  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.48  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.48  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.48  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.48  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.48  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.48  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.48  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.48  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.20/0.48  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.48  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.48  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.48  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.20/0.48  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.48  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.20/0.48  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.48  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.20/0.48  fof(c_0_20, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.48  fof(c_0_21, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.48  fof(c_0_22, plain, ![X42]:(((v1_funct_1(X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(v1_funct_2(X42,k1_relat_1(X42),k2_relat_1(X42))|(~v1_relat_1(X42)|~v1_funct_1(X42))))&(m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X42),k2_relat_1(X42))))|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.48  fof(c_0_23, plain, ![X24]:((k2_relat_1(X24)=k1_relat_1(k2_funct_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(k1_relat_1(X24)=k2_relat_1(k2_funct_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.48  fof(c_0_24, plain, ![X21]:((v1_relat_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(v1_funct_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.48  fof(c_0_25, plain, ![X37, X38, X39]:((((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X38=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&((~v1_funct_2(X39,X37,X38)|X37=k1_relset_1(X37,X38,X39)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X37!=k1_relset_1(X37,X38,X39)|v1_funct_2(X39,X37,X38)|X37!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))))&((~v1_funct_2(X39,X37,X38)|X39=k1_xboole_0|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(X39!=k1_xboole_0|v1_funct_2(X39,X37,X38)|X37=k1_xboole_0|X38!=k1_xboole_0|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.48  cnf(c_0_26, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  fof(c_0_28, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|v1_relat_1(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.48  cnf(c_0_29, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_30, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  cnf(c_0_31, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.48  cnf(c_0_32, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.48  cnf(c_0_33, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.48  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  cnf(c_0_35, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.48  cnf(c_0_36, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.48  fof(c_0_37, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.48  fof(c_0_38, plain, ![X40]:(v1_partfun1(k6_partfun1(X40),X40)&m1_subset_1(k6_partfun1(X40),k1_zfmisc_1(k2_zfmisc_1(X40,X40)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.48  fof(c_0_39, plain, ![X41]:k6_partfun1(X41)=k6_relat_1(X41), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.48  fof(c_0_40, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.48  cnf(c_0_41, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  cnf(c_0_43, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.48  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|esk2_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.48  cnf(c_0_45, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_36, c_0_27])).
% 0.20/0.48  cnf(c_0_47, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.48  cnf(c_0_48, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  cnf(c_0_49, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.48  cnf(c_0_50, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.48  cnf(c_0_51, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.48  cnf(c_0_52, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_53, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_relat_1(esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_42])])).
% 0.20/0.48  cnf(c_0_54, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_42]), c_0_46])])).
% 0.20/0.48  cnf(c_0_55, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  cnf(c_0_56, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_27]), c_0_48])).
% 0.20/0.48  fof(c_0_57, plain, ![X5, X6]:(~v1_xboole_0(X5)|X5=X6|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.20/0.48  fof(c_0_58, plain, ![X10, X11]:(~v1_xboole_0(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.48  cnf(c_0_59, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.48  cnf(c_0_60, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.48  cnf(c_0_61, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_30]), c_0_31]), c_0_32])).
% 0.20/0.48  cnf(c_0_62, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_46])])).
% 0.20/0.48  cnf(c_0_63, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_45]), c_0_42]), c_0_46])])).
% 0.20/0.48  cnf(c_0_64, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.48  cnf(c_0_65, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.48  cnf(c_0_66, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.48  cnf(c_0_67, plain, (m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.48  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_56]), c_0_42]), c_0_46])])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_44]), c_0_45]), c_0_42]), c_0_46])])).
% 0.20/0.48  cnf(c_0_70, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.48  cnf(c_0_71, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.48  fof(c_0_72, plain, ![X19]:(k1_relat_1(k6_relat_1(X19))=X19&k2_relat_1(k6_relat_1(X19))=X19), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.20/0.48  cnf(c_0_73, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_64]), c_0_60]), c_0_65])])).
% 0.20/0.48  cnf(c_0_74, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_65])])).
% 0.20/0.48  fof(c_0_75, plain, ![X20]:(~v1_xboole_0(X20)|v1_funct_1(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.20/0.48  fof(c_0_76, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.48  cnf(c_0_77, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))), inference(spm,[status(thm)],[c_0_66, c_0_68])).
% 0.20/0.48  cnf(c_0_78, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_55]), c_0_56]), c_0_45]), c_0_42]), c_0_46])]), c_0_70])).
% 0.20/0.48  cnf(c_0_79, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_71])).
% 0.20/0.48  cnf(c_0_80, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.48  cnf(c_0_81, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.48  cnf(c_0_82, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.20/0.48  cnf(c_0_83, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.20/0.48  cnf(c_0_84, negated_conjecture, (v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_65])])).
% 0.20/0.48  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.48  cnf(c_0_86, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_65])).
% 0.20/0.48  cnf(c_0_87, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_60])).
% 0.20/0.48  cnf(c_0_88, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_84])).
% 0.20/0.48  cnf(c_0_89, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),k1_xboole_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_78]), c_0_78]), c_0_60])).
% 0.20/0.48  cnf(c_0_90, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_85]), c_0_79]), c_0_86]), c_0_87])])).
% 0.20/0.48  cnf(c_0_91, negated_conjecture, (v2_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_45, c_0_88])).
% 0.20/0.48  cnf(c_0_92, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk1_0)|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_88]), c_0_88])).
% 0.20/0.48  cnf(c_0_93, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.20/0.48  fof(c_0_94, plain, ![X43, X44]:(((v1_funct_1(X44)|~r1_tarski(k2_relat_1(X44),X43)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(v1_funct_2(X44,k1_relat_1(X44),X43)|~r1_tarski(k2_relat_1(X44),X43)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),X43)))|~r1_tarski(k2_relat_1(X44),X43)|(~v1_relat_1(X44)|~v1_funct_1(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.20/0.48  cnf(c_0_95, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.48  fof(c_0_96, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.48  cnf(c_0_97, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])])).
% 0.20/0.48  cnf(c_0_98, plain, (v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_93]), c_0_65])])).
% 0.20/0.48  cnf(c_0_99, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.20/0.48  cnf(c_0_100, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_95, c_0_81])).
% 0.20/0.48  cnf(c_0_101, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.20/0.48  cnf(c_0_102, negated_conjecture, (~v1_funct_2(X1,k1_xboole_0,esk1_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_64]), c_0_98])])).
% 0.20/0.48  cnf(c_0_103, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_86]), c_0_87]), c_0_101])]), c_0_85])).
% 0.20/0.48  cnf(c_0_104, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_65])]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 105
% 0.20/0.48  # Proof object clause steps            : 67
% 0.20/0.48  # Proof object formula steps           : 38
% 0.20/0.48  # Proof object conjectures             : 30
% 0.20/0.48  # Proof object clause conjectures      : 27
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 29
% 0.20/0.48  # Proof object initial formulas used   : 19
% 0.20/0.48  # Proof object generating inferences   : 28
% 0.20/0.48  # Proof object simplifying inferences  : 71
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 25
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 45
% 0.20/0.48  # Removed in clause preprocessing      : 3
% 0.20/0.48  # Initial clauses in saturation        : 42
% 0.20/0.48  # Processed clauses                    : 739
% 0.20/0.48  # ...of these trivial                  : 18
% 0.20/0.48  # ...subsumed                          : 378
% 0.20/0.48  # ...remaining for further processing  : 343
% 0.20/0.48  # Other redundant clauses eliminated   : 23
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 9
% 0.20/0.48  # Backward-rewritten                   : 98
% 0.20/0.48  # Generated clauses                    : 2535
% 0.20/0.48  # ...of the previous two non-trivial   : 2423
% 0.20/0.48  # Contextual simplify-reflections      : 14
% 0.20/0.48  # Paramodulations                      : 2513
% 0.20/0.48  # Factorizations                       : 0
% 0.20/0.48  # Equation resolutions                 : 23
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 188
% 0.20/0.48  #    Positive orientable unit clauses  : 33
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 1
% 0.20/0.48  #    Non-unit-clauses                  : 154
% 0.20/0.48  # Current number of unprocessed clauses: 1735
% 0.20/0.48  # ...number of literals in the above   : 8140
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 150
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 14301
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 8997
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 401
% 0.20/0.48  # Unit Clause-clause subsumption calls : 473
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 34
% 0.20/0.48  # BW rewrite match successes           : 13
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 31182
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.133 s
% 0.20/0.48  # System time              : 0.007 s
% 0.20/0.48  # Total time               : 0.139 s
% 0.20/0.48  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
