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
% DateTime   : Thu Dec  3 11:02:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 (1582 expanded)
%              Number of clauses        :   75 ( 615 expanded)
%              Number of leaves         :   21 ( 401 expanded)
%              Depth                    :   16
%              Number of atoms          :  300 (7288 expanded)
%              Number of equality atoms :   79 (1375 expanded)
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

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

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v2_funct_1(esk5_0)
    & k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0
    & ( ~ v1_funct_1(k2_funct_1(esk5_0))
      | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_24,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X44] :
      ( ( v1_funct_1(X44)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( v1_funct_2(X44,k1_relat_1(X44),k2_relat_1(X44))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),k2_relat_1(X44))))
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_26,plain,(
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

fof(c_0_27,plain,(
    ! [X22] :
      ( ( v1_relat_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( v1_funct_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_28,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v1_funct_2(X38,X36,X37)
        | X36 = k1_relset_1(X36,X37,X38)
        | X37 = k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X36 != k1_relset_1(X36,X37,X38)
        | v1_funct_2(X38,X36,X37)
        | X37 = k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( ~ v1_funct_2(X38,X36,X37)
        | X36 = k1_relset_1(X36,X37,X38)
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X36 != k1_relset_1(X36,X37,X38)
        | v1_funct_2(X38,X36,X37)
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( ~ v1_funct_2(X38,X36,X37)
        | X38 = k1_xboole_0
        | X36 = k1_xboole_0
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( X38 != k1_xboole_0
        | v1_funct_2(X38,X36,X37)
        | X36 = k1_xboole_0
        | X37 != k1_xboole_0
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_29,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_31,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_32,plain,(
    ! [X40,X41] :
      ( m1_subset_1(esk2_2(X40,X41),k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      & v1_relat_1(esk2_2(X40,X41))
      & v4_relat_1(esk2_2(X40,X41),X40)
      & v5_relat_1(esk2_2(X40,X41),X41)
      & v1_funct_1(esk2_2(X40,X41))
      & v1_funct_2(esk2_2(X40,X41),X40,X41) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_33,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_34,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_35,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_37,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_43,plain,(
    ! [X16,X17] :
      ( ~ v1_xboole_0(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v1_xboole_0(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_33])).

fof(c_0_46,plain,(
    ! [X39] :
      ( v1_partfun1(k6_partfun1(X39),X39)
      & m1_subset_1(k6_partfun1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_47,plain,(
    ! [X43] : k6_partfun1(X43) = k6_relat_1(X43) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_48,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_52,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_30]),c_0_40])]),c_0_41])).

cnf(c_0_54,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

fof(c_0_56,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,plain,
    ( m1_subset_1(esk2_2(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_60,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_61,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_62,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(X12))
      | ~ r2_hidden(X14,X13)
      | r2_hidden(X14,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_64,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_relat_1(esk5_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_38]),c_0_51])])).

cnf(c_0_66,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),k1_relat_1(k2_funct_1(esk5_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_51]),c_0_55])])).

cnf(c_0_67,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,plain,
    ( v1_xboole_0(esk2_2(k1_xboole_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

cnf(c_0_70,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_51]),c_0_55])])).

fof(c_0_73,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_74,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_36]),c_0_37]),c_0_38])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_55])])).

cnf(c_0_76,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_64]),c_0_54]),c_0_51]),c_0_55])])).

fof(c_0_77,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | ~ r1_tarski(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_78,plain,(
    ! [X9] : r1_tarski(k1_xboole_0,X9) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_79,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_80,plain,
    ( v1_funct_2(esk2_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_81,plain,
    ( esk2_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

fof(c_0_82,plain,(
    ! [X15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_83,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_45])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_85,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_86,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_53]),c_0_54]),c_0_51]),c_0_55])])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_88,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_89,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_91,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_79]),c_0_45])).

cnf(c_0_92,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_93,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_94,plain,(
    ! [X23] :
      ( v1_relat_1(k6_relat_1(X23))
      & v1_funct_1(k6_relat_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_95,plain,
    ( v1_xboole_0(k6_relat_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_83]),c_0_59])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))
    | v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_97,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_67]),c_0_64]),c_0_54]),c_0_51]),c_0_55])]),c_0_87])).

cnf(c_0_98,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_99,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,plain,
    ( k1_relset_1(k1_xboole_0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])])).

cnf(c_0_101,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_93])).

cnf(c_0_102,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_103,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_97]),c_0_98]),c_0_99])).

cnf(c_0_105,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_106,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_107,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_93])).

cnf(c_0_108,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_104])).

cnf(c_0_109,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v2_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_105]),c_0_98]),c_0_106]),c_0_107])])).

cnf(c_0_110,negated_conjecture,
    ( v2_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_108])).

cnf(c_0_111,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_97]),c_0_97]),c_0_45]),c_0_108]),c_0_108])).

cnf(c_0_113,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_111]),c_0_59])])).

cnf(c_0_114,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_111])])).

cnf(c_0_115,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_113])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_92])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.20/0.39  # and selection function SelectNewComplexAHPNS.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.39  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.20/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.20/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.20/0.39  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.20/0.39  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.20/0.39  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.39  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.39  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.20/0.39  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.20/0.39  fof(c_0_22, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.39  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v2_funct_1(esk5_0)&k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0)&(~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.39  fof(c_0_24, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X44]:(((v1_funct_1(X44)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(v1_funct_2(X44,k1_relat_1(X44),k2_relat_1(X44))|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X44),k2_relat_1(X44))))|(~v1_relat_1(X44)|~v1_funct_1(X44)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.20/0.39  fof(c_0_26, plain, ![X24]:((k2_relat_1(X24)=k1_relat_1(k2_funct_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))&(k1_relat_1(X24)=k2_relat_1(k2_funct_1(X24))|~v2_funct_1(X24)|(~v1_relat_1(X24)|~v1_funct_1(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.39  fof(c_0_27, plain, ![X22]:((v1_relat_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(v1_funct_1(k2_funct_1(X22))|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.20/0.39  fof(c_0_28, plain, ![X36, X37, X38]:((((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&((~v1_funct_2(X38,X36,X37)|X38=k1_xboole_0|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X38!=k1_xboole_0|v1_funct_2(X38,X36,X37)|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.39  cnf(c_0_29, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  fof(c_0_31, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  fof(c_0_32, plain, ![X40, X41]:(((((m1_subset_1(esk2_2(X40,X41),k1_zfmisc_1(k2_zfmisc_1(X40,X41)))&v1_relat_1(esk2_2(X40,X41)))&v4_relat_1(esk2_2(X40,X41),X40))&v5_relat_1(esk2_2(X40,X41),X41))&v1_funct_1(esk2_2(X40,X41)))&v1_funct_2(esk2_2(X40,X41),X40,X41)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.20/0.39  cnf(c_0_33, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_34, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_relset_1(X33,X34,X35)=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  cnf(c_0_35, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_36, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_37, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_38, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_39, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.39  cnf(c_0_42, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.39  fof(c_0_43, plain, ![X16, X17]:(~v1_xboole_0(X16)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v1_xboole_0(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.20/0.39  cnf(c_0_44, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_45, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.39  fof(c_0_46, plain, ![X39]:(v1_partfun1(k6_partfun1(X39),X39)&m1_subset_1(k6_partfun1(X39),k1_zfmisc_1(k2_zfmisc_1(X39,X39)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.20/0.39  fof(c_0_47, plain, ![X43]:k6_partfun1(X43)=k6_relat_1(X43), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.20/0.39  cnf(c_0_48, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_51, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_52, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_30]), c_0_40])]), c_0_41])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.20/0.39  fof(c_0_56, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.39  cnf(c_0_57, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_58, plain, (m1_subset_1(esk2_2(k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.39  cnf(c_0_59, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  cnf(c_0_60, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.39  cnf(c_0_61, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.39  fof(c_0_62, plain, ![X12, X13, X14]:(~m1_subset_1(X13,k1_zfmisc_1(X12))|(~r2_hidden(X14,X13)|r2_hidden(X14,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.39  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_30]), c_0_49])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_relat_1(esk5_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_38]), c_0_51])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),k1_relat_1(k2_funct_1(esk5_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_51]), c_0_55])])).
% 0.20/0.39  cnf(c_0_67, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.39  cnf(c_0_68, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.20/0.39  cnf(c_0_69, plain, (v1_xboole_0(esk2_2(k1_xboole_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.20/0.39  cnf(c_0_70, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.39  cnf(c_0_71, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_51]), c_0_55])])).
% 0.20/0.39  fof(c_0_73, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.39  cnf(c_0_74, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_36]), c_0_37]), c_0_38])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_55])])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (esk4_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_64]), c_0_54]), c_0_51]), c_0_55])])).
% 0.20/0.39  fof(c_0_77, plain, ![X25, X26]:(~r2_hidden(X25,X26)|~r1_tarski(X26,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.39  fof(c_0_78, plain, ![X9]:r1_tarski(k1_xboole_0,X9), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.39  cnf(c_0_79, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_80, plain, (v1_funct_2(esk2_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_81, plain, (esk2_2(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.39  fof(c_0_82, plain, ![X15]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.39  cnf(c_0_83, plain, (m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_45])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.39  cnf(c_0_85, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.39  cnf(c_0_86, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_53]), c_0_54]), c_0_51]), c_0_55])])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (esk4_0=k1_xboole_0|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.39  cnf(c_0_88, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_89, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.39  cnf(c_0_90, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.20/0.39  cnf(c_0_91, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_79]), c_0_45])).
% 0.20/0.39  cnf(c_0_92, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.20/0.39  cnf(c_0_93, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.20/0.39  fof(c_0_94, plain, ![X23]:(v1_relat_1(k6_relat_1(X23))&v1_funct_1(k6_relat_1(X23))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.20/0.39  cnf(c_0_95, plain, (v1_xboole_0(k6_relat_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_83]), c_0_59])])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, (r2_hidden(esk1_1(esk5_0),k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))|v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.20/0.39  cnf(c_0_97, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_67]), c_0_64]), c_0_54]), c_0_51]), c_0_55])]), c_0_87])).
% 0.20/0.39  cnf(c_0_98, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_88])).
% 0.20/0.39  cnf(c_0_99, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.39  cnf(c_0_100, plain, (k1_relset_1(k1_xboole_0,X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])])).
% 0.20/0.39  cnf(c_0_101, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_93])).
% 0.20/0.39  cnf(c_0_102, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.20/0.39  cnf(c_0_103, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_95])).
% 0.20/0.39  cnf(c_0_104, negated_conjecture, (v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_96, c_0_97]), c_0_98]), c_0_99])).
% 0.20/0.39  cnf(c_0_105, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_100, c_0_101])).
% 0.20/0.39  cnf(c_0_106, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_102, c_0_103])).
% 0.20/0.39  cnf(c_0_107, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_93])).
% 0.20/0.39  cnf(c_0_108, negated_conjecture, (esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_104])).
% 0.20/0.39  cnf(c_0_109, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|~v2_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_105]), c_0_98]), c_0_106]), c_0_107])])).
% 0.20/0.39  cnf(c_0_110, negated_conjecture, (v2_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_54, c_0_108])).
% 0.20/0.39  cnf(c_0_111, plain, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 0.20/0.39  cnf(c_0_112, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_97]), c_0_97]), c_0_45]), c_0_108]), c_0_108])).
% 0.20/0.39  cnf(c_0_113, plain, (v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_111]), c_0_59])])).
% 0.20/0.39  cnf(c_0_114, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_111])])).
% 0.20/0.39  cnf(c_0_115, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_113])).
% 0.20/0.39  cnf(c_0_116, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_92])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 117
% 0.20/0.39  # Proof object clause steps            : 75
% 0.20/0.39  # Proof object formula steps           : 42
% 0.20/0.39  # Proof object conjectures             : 29
% 0.20/0.39  # Proof object clause conjectures      : 26
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 32
% 0.20/0.39  # Proof object initial formulas used   : 21
% 0.20/0.39  # Proof object generating inferences   : 31
% 0.20/0.39  # Proof object simplifying inferences  : 68
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 23
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 48
% 0.20/0.39  # Removed in clause preprocessing      : 2
% 0.20/0.39  # Initial clauses in saturation        : 46
% 0.20/0.39  # Processed clauses                    : 257
% 0.20/0.39  # ...of these trivial                  : 16
% 0.20/0.39  # ...subsumed                          : 30
% 0.20/0.39  # ...remaining for further processing  : 211
% 0.20/0.39  # Other redundant clauses eliminated   : 11
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 2
% 0.20/0.39  # Backward-rewritten                   : 64
% 0.20/0.39  # Generated clauses                    : 323
% 0.20/0.39  # ...of the previous two non-trivial   : 256
% 0.20/0.39  # Contextual simplify-reflections      : 9
% 0.20/0.39  # Paramodulations                      : 313
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 11
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 93
% 0.20/0.39  #    Positive orientable unit clauses  : 37
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 55
% 0.20/0.39  # Current number of unprocessed clauses: 83
% 0.20/0.39  # ...number of literals in the above   : 296
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 113
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 703
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 339
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 29
% 0.20/0.39  # Unit Clause-clause subsumption calls : 125
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 76
% 0.20/0.39  # BW rewrite match successes           : 19
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 7509
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.042 s
% 0.20/0.39  # System time              : 0.004 s
% 0.20/0.39  # Total time               : 0.046 s
% 0.20/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
