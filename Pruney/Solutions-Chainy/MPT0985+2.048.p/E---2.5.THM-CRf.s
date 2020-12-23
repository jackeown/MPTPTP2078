%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:39 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  128 (10062 expanded)
%              Number of clauses        :   89 (3781 expanded)
%              Number of leaves         :   19 (2547 expanded)
%              Depth                    :   17
%              Number of atoms          :  394 (48545 expanded)
%              Number of equality atoms :   90 (6353 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   2 average)
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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

fof(t9_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(rc2_partfun1,axiom,(
    ! [X1] :
    ? [X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      & v1_relat_1(X2)
      & v4_relat_1(X2,X1)
      & v5_relat_1(X2,X1)
      & v1_relat_2(X2)
      & v3_relat_2(X2)
      & v4_relat_2(X2)
      & v8_relat_2(X2)
      & v1_partfun1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_partfun1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

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
    ! [X43] :
      ( ( v1_funct_1(X43)
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( v1_funct_2(X43,k1_relat_1(X43),k2_relat_1(X43))
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) )
      & ( m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X43),k2_relat_1(X43))))
        | ~ v1_relat_1(X43)
        | ~ v1_funct_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_21,plain,(
    ! [X28] :
      ( ( k2_relat_1(X28) = k1_relat_1(k2_funct_1(X28))
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( k1_relat_1(X28) = k2_relat_1(k2_funct_1(X28))
        | ~ v2_funct_1(X28)
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_22,plain,(
    ! [X26] :
      ( ( v1_relat_1(k2_funct_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( v1_funct_1(k2_funct_1(X26))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_23,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_relset_1(X35,X36,X37) = k2_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v2_funct_1(esk5_0)
    & k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0
    & ( ~ v1_funct_1(k2_funct_1(esk5_0))
      | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_25,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_40,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_41,plain,(
    ! [X44,X45,X46,X47] :
      ( ( v1_funct_1(X47)
        | X45 = k1_xboole_0
        | ~ r1_tarski(X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X44,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(X47,X44,X46)
        | X45 = k1_xboole_0
        | ~ r1_tarski(X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X44,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X46)))
        | X45 = k1_xboole_0
        | ~ r1_tarski(X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X44,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_1(X47)
        | X44 != k1_xboole_0
        | ~ r1_tarski(X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X44,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(X47,X44,X46)
        | X44 != k1_xboole_0
        | ~ r1_tarski(X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X44,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X46)))
        | X44 != k1_xboole_0
        | ~ r1_tarski(X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X44,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_43,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_37]),c_0_38]),c_0_39])])).

fof(c_0_45,plain,(
    ! [X32,X33,X34] :
      ( ( v4_relat_1(X34,X32)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v5_relat_1(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_46,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_47,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_37]),c_0_38]),c_0_39])])).

fof(c_0_50,plain,(
    ! [X16,X17] :
      ( ( ~ v4_relat_1(X17,X16)
        | r1_tarski(k1_relat_1(X17),X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r1_tarski(k1_relat_1(X17),X16)
        | v4_relat_1(X17,X16)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_52,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_53,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_31])).

fof(c_0_59,plain,(
    ! [X18,X19] :
      ( ( ~ v5_relat_1(X19,X18)
        | r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k2_relat_1(X19),X18)
        | v5_relat_1(X19,X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_60,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_relat_1(esk5_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_29]),c_0_38])])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_29]),c_0_38]),c_0_39])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_39])])).

fof(c_0_68,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_69,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_72,plain,(
    ! [X41] :
      ( m1_subset_1(esk2_1(X41),k1_zfmisc_1(k2_zfmisc_1(X41,X41)))
      & v1_relat_1(esk2_1(X41))
      & v4_relat_1(esk2_1(X41),X41)
      & v5_relat_1(esk2_1(X41),X41)
      & v1_relat_2(esk2_1(X41))
      & v3_relat_2(esk2_1(X41))
      & v4_relat_2(esk2_1(X41))
      & v8_relat_2(esk2_1(X41))
      & v1_partfun1(esk2_1(X41),X41) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_partfun1])])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_48]),c_0_49])])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_39])])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

fof(c_0_76,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X24))
      | v1_funct_1(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

cnf(c_0_77,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_79,plain,
    ( v5_relat_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_80,plain,
    ( v1_relat_1(esk2_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_81,plain,(
    ! [X22] :
      ( ( k1_relat_1(X22) != k1_xboole_0
        | X22 = k1_xboole_0
        | ~ v1_relat_1(X22) )
      & ( k2_relat_1(X22) != k1_xboole_0
        | X22 = k1_xboole_0
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_82,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_29]),c_0_38]),c_0_39])])).

cnf(c_0_83,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( k2_relset_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)),k2_funct_1(esk5_0)) = k2_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_42])).

cnf(c_0_85,negated_conjecture,
    ( k2_relset_1(esk4_0,k1_relat_1(esk5_0),k2_funct_1(esk5_0)) = k2_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_48])).

cnf(c_0_86,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_87,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_88,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_89,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | ~ r1_tarski(X1,k2_relat_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_relat_1(esk2_1(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_79]),c_0_80])])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_67]),c_0_83])).

fof(c_0_93,plain,(
    ! [X23] :
      ( ( k1_relat_1(X23) != k1_xboole_0
        | k2_relat_1(X23) = k1_xboole_0
        | ~ v1_relat_1(X23) )
      & ( k2_relat_1(X23) != k1_xboole_0
        | k1_relat_1(X23) = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_94,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_95,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk5_0)) = k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_43]),c_0_85]),c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_96,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

cnf(c_0_97,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_61])).

fof(c_0_98,plain,(
    ! [X38,X39,X40] :
      ( ( v1_funct_1(X40)
        | ~ v1_funct_1(X40)
        | ~ v1_partfun1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( v1_funct_2(X40,X38,X39)
        | ~ v1_funct_1(X40)
        | ~ v1_partfun1(X40,X38)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_99,plain,
    ( v1_funct_1(esk2_1(X1))
    | ~ v1_funct_1(k2_zfmisc_1(X1,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_62])])).

cnf(c_0_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_101,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_61])).

cnf(c_0_102,plain,
    ( k2_relat_1(esk2_1(k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_103,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_39])])).

cnf(c_0_104,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_105,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | k1_relat_1(esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96])])).

cnf(c_0_106,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_97]),c_0_71])])).

cnf(c_0_107,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_108,plain,
    ( v1_funct_1(esk2_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_109,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_38]),c_0_39])])).

cnf(c_0_110,plain,
    ( esk2_1(k2_relat_1(k1_xboole_0)) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_102]),c_0_80])])).

cnf(c_0_111,negated_conjecture,
    ( k2_relat_1(k1_xboole_0) = esk4_0 ),
    inference(rw,[status(thm)],[c_0_36,c_0_103])).

cnf(c_0_112,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk5_0)) = k1_xboole_0
    | k1_relat_1(esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_95]),c_0_96])])).

cnf(c_0_113,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105,c_0_92])]),c_0_103])).

cnf(c_0_114,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_106])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_103]),c_0_103])).

cnf(c_0_116,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ v1_partfun1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_107,c_0_100])).

cnf(c_0_117,plain,
    ( v1_partfun1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_118,plain,
    ( v1_funct_1(esk2_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_109])])).

cnf(c_0_119,plain,
    ( m1_subset_1(esk2_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_100])).

cnf(c_0_120,plain,
    ( esk2_1(esk4_0) = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110,c_0_111]),c_0_111])).

cnf(c_0_121,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_92])]),c_0_103]),c_0_113]),c_0_114]),c_0_111])).

cnf(c_0_122,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_113]),c_0_113]),c_0_61])])).

cnf(c_0_123,plain,
    ( v1_funct_2(esk2_1(k1_xboole_0),k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118]),c_0_119])])).

cnf(c_0_124,plain,
    ( esk2_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120,c_0_121]),c_0_121])])).

cnf(c_0_125,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_122,c_0_121])).

cnf(c_0_126,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_123,c_0_124])).

cnf(c_0_127,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_126])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.13/0.40  # and selection function SelectNewComplexAHPNS.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.030 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.13/0.40  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.13/0.40  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.13/0.40  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.13/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.40  fof(t9_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.13/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.40  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.13/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.13/0.40  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(rc2_partfun1, axiom, ![X1]:?[X2]:((((((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))&v1_relat_1(X2))&v4_relat_1(X2,X1))&v5_relat_1(X2,X1))&v1_relat_2(X2))&v3_relat_2(X2))&v4_relat_2(X2))&v8_relat_2(X2))&v1_partfun1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_partfun1)).
% 0.13/0.40  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.13/0.40  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.13/0.40  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.13/0.40  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.13/0.40  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.13/0.40  fof(c_0_20, plain, ![X43]:(((v1_funct_1(X43)|(~v1_relat_1(X43)|~v1_funct_1(X43)))&(v1_funct_2(X43,k1_relat_1(X43),k2_relat_1(X43))|(~v1_relat_1(X43)|~v1_funct_1(X43))))&(m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X43),k2_relat_1(X43))))|(~v1_relat_1(X43)|~v1_funct_1(X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.13/0.40  fof(c_0_21, plain, ![X28]:((k2_relat_1(X28)=k1_relat_1(k2_funct_1(X28))|~v2_funct_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(k1_relat_1(X28)=k2_relat_1(k2_funct_1(X28))|~v2_funct_1(X28)|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.13/0.40  fof(c_0_22, plain, ![X26]:((v1_relat_1(k2_funct_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(v1_funct_1(k2_funct_1(X26))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.13/0.40  fof(c_0_23, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_relset_1(X35,X36,X37)=k2_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.40  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v2_funct_1(esk5_0)&k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0)&(~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.13/0.40  fof(c_0_25, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.40  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_27, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_28, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_29, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.40  cnf(c_0_30, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_33, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.40  cnf(c_0_34, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_35, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 0.13/0.40  cnf(c_0_40, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_28]), c_0_29])).
% 0.13/0.40  fof(c_0_41, plain, ![X44, X45, X46, X47]:((((v1_funct_1(X47)|X45=k1_xboole_0|~r1_tarski(X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(v1_funct_2(X47,X44,X46)|X45=k1_xboole_0|~r1_tarski(X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X46)))|X45=k1_xboole_0|~r1_tarski(X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&(((v1_funct_1(X47)|X44!=k1_xboole_0|~r1_tarski(X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(v1_funct_2(X47,X44,X46)|X44!=k1_xboole_0|~r1_tarski(X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X46)))|X44!=k1_xboole_0|~r1_tarski(X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,X44,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.40  cnf(c_0_43, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.40  fof(c_0_45, plain, ![X32, X33, X34]:((v4_relat_1(X34,X32)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(v5_relat_1(X34,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.40  fof(c_0_46, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.40  cnf(c_0_47, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.40  fof(c_0_50, plain, ![X16, X17]:((~v4_relat_1(X17,X16)|r1_tarski(k1_relat_1(X17),X16)|~v1_relat_1(X17))&(~r1_tarski(k1_relat_1(X17),X16)|v4_relat_1(X17,X16)|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.13/0.40  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.40  fof(c_0_52, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.40  fof(c_0_53, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.13/0.40  cnf(c_0_54, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)|~v1_funct_1(k2_funct_1(esk5_0))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.13/0.40  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_51, c_0_31])).
% 0.13/0.40  fof(c_0_59, plain, ![X18, X19]:((~v5_relat_1(X19,X18)|r1_tarski(k2_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_tarski(k2_relat_1(X19),X18)|v5_relat_1(X19,X18)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.13/0.40  cnf(c_0_60, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.40  cnf(c_0_61, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.40  cnf(c_0_62, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.40  cnf(c_0_63, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_54])).
% 0.13/0.40  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.13/0.40  cnf(c_0_65, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_relat_1(esk5_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_29]), c_0_38])])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_29]), c_0_38]), c_0_39])])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_39])])).
% 0.13/0.40  fof(c_0_68, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  cnf(c_0_69, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.13/0.40  cnf(c_0_70, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.13/0.40  cnf(c_0_71, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.13/0.40  fof(c_0_72, plain, ![X41]:((((((((m1_subset_1(esk2_1(X41),k1_zfmisc_1(k2_zfmisc_1(X41,X41)))&v1_relat_1(esk2_1(X41)))&v4_relat_1(esk2_1(X41),X41))&v5_relat_1(esk2_1(X41),X41))&v1_relat_2(esk2_1(X41)))&v3_relat_2(esk2_1(X41)))&v4_relat_2(esk2_1(X41)))&v8_relat_2(esk2_1(X41)))&v1_partfun1(esk2_1(X41),X41)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc2_partfun1])])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~v1_funct_1(k2_funct_1(esk5_0))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_48]), c_0_49])])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_39])])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.13/0.40  fof(c_0_76, plain, ![X24, X25]:(~v1_relat_1(X24)|~v1_funct_1(X24)|(~m1_subset_1(X25,k1_zfmisc_1(X24))|v1_funct_1(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.13/0.40  cnf(c_0_77, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.13/0.40  cnf(c_0_78, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.13/0.40  cnf(c_0_79, plain, (v5_relat_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.40  cnf(c_0_80, plain, (v1_relat_1(esk2_1(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.40  fof(c_0_81, plain, ![X22]:((k1_relat_1(X22)!=k1_xboole_0|X22=k1_xboole_0|~v1_relat_1(X22))&(k2_relat_1(X22)!=k1_xboole_0|X22=k1_xboole_0|~v1_relat_1(X22))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_29]), c_0_38]), c_0_39])])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (k2_relset_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)),k2_funct_1(esk5_0))=k2_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_42])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, (k2_relset_1(esk4_0,k1_relat_1(esk5_0),k2_funct_1(esk5_0))=k2_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_48])).
% 0.13/0.40  cnf(c_0_86, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.13/0.40  cnf(c_0_87, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.40  cnf(c_0_88, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_89, plain, (X1=k2_relat_1(k1_xboole_0)|~r1_tarski(X1,k2_relat_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.40  cnf(c_0_90, plain, (r1_tarski(k2_relat_1(esk2_1(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_79]), c_0_80])])).
% 0.13/0.40  cnf(c_0_91, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.13/0.40  cnf(c_0_92, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_67]), c_0_83])).
% 0.13/0.40  fof(c_0_93, plain, ![X23]:((k1_relat_1(X23)!=k1_xboole_0|k2_relat_1(X23)=k1_xboole_0|~v1_relat_1(X23))&(k2_relat_1(X23)!=k1_xboole_0|k1_relat_1(X23)=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.13/0.40  cnf(c_0_94, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_81])).
% 0.13/0.40  cnf(c_0_95, negated_conjecture, (k2_relat_1(k2_funct_1(esk5_0))=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_43]), c_0_85]), c_0_37]), c_0_38]), c_0_39])])).
% 0.13/0.40  cnf(c_0_96, negated_conjecture, (v1_relat_1(k2_funct_1(esk5_0))), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 0.13/0.40  cnf(c_0_97, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_61])).
% 0.13/0.40  fof(c_0_98, plain, ![X38, X39, X40]:((v1_funct_1(X40)|(~v1_funct_1(X40)|~v1_partfun1(X40,X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(v1_funct_2(X40,X38,X39)|(~v1_funct_1(X40)|~v1_partfun1(X40,X38))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.13/0.40  cnf(c_0_99, plain, (v1_funct_1(esk2_1(X1))|~v1_funct_1(k2_zfmisc_1(X1,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_62])])).
% 0.13/0.40  cnf(c_0_100, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_88])).
% 0.13/0.40  cnf(c_0_101, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_86, c_0_61])).
% 0.13/0.40  cnf(c_0_102, plain, (k2_relat_1(esk2_1(k2_relat_1(k1_xboole_0)))=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.13/0.40  cnf(c_0_103, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_39])])).
% 0.13/0.40  cnf(c_0_104, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.13/0.40  cnf(c_0_105, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|k1_relat_1(esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96])])).
% 0.13/0.40  cnf(c_0_106, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_97]), c_0_71])])).
% 0.13/0.40  cnf(c_0_107, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_98])).
% 0.13/0.40  cnf(c_0_108, plain, (v1_funct_1(esk2_1(k1_xboole_0))|~v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.13/0.40  cnf(c_0_109, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_38]), c_0_39])])).
% 0.13/0.40  cnf(c_0_110, plain, (esk2_1(k2_relat_1(k1_xboole_0))=k1_xboole_0|k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_102]), c_0_80])])).
% 0.13/0.40  cnf(c_0_111, negated_conjecture, (k2_relat_1(k1_xboole_0)=esk4_0), inference(rw,[status(thm)],[c_0_36, c_0_103])).
% 0.13/0.40  cnf(c_0_112, negated_conjecture, (k1_relat_1(k2_funct_1(esk5_0))=k1_xboole_0|k1_relat_1(esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_95]), c_0_96])])).
% 0.13/0.40  cnf(c_0_113, negated_conjecture, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_105, c_0_92])]), c_0_103])).
% 0.13/0.40  cnf(c_0_114, plain, (k1_relat_1(k1_xboole_0)=k2_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_106])).
% 0.13/0.40  cnf(c_0_115, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_103]), c_0_103])).
% 0.13/0.40  cnf(c_0_116, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~v1_partfun1(X1,k1_xboole_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_107, c_0_100])).
% 0.13/0.40  cnf(c_0_117, plain, (v1_partfun1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.13/0.40  cnf(c_0_118, plain, (v1_funct_1(esk2_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_109])])).
% 0.13/0.40  cnf(c_0_119, plain, (m1_subset_1(esk2_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_87, c_0_100])).
% 0.13/0.40  cnf(c_0_120, plain, (esk2_1(esk4_0)=k1_xboole_0|esk4_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_110, c_0_111]), c_0_111])).
% 0.13/0.40  cnf(c_0_121, negated_conjecture, (esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_92])]), c_0_103]), c_0_113]), c_0_114]), c_0_111])).
% 0.13/0.40  cnf(c_0_122, negated_conjecture, (~v1_funct_2(k1_xboole_0,esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_113]), c_0_113]), c_0_61])])).
% 0.13/0.40  cnf(c_0_123, plain, (v1_funct_2(esk2_1(k1_xboole_0),k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118]), c_0_119])])).
% 0.13/0.40  cnf(c_0_124, plain, (esk2_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_120, c_0_121]), c_0_121])])).
% 0.13/0.40  cnf(c_0_125, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)), inference(rw,[status(thm)],[c_0_122, c_0_121])).
% 0.13/0.40  cnf(c_0_126, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(rw,[status(thm)],[c_0_123, c_0_124])).
% 0.13/0.40  cnf(c_0_127, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_126])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 128
% 0.13/0.40  # Proof object clause steps            : 89
% 0.13/0.40  # Proof object formula steps           : 39
% 0.13/0.40  # Proof object conjectures             : 40
% 0.13/0.40  # Proof object clause conjectures      : 37
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 33
% 0.13/0.40  # Proof object initial formulas used   : 19
% 0.13/0.40  # Proof object generating inferences   : 42
% 0.13/0.40  # Proof object simplifying inferences  : 93
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 22
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 56
% 0.13/0.40  # Removed in clause preprocessing      : 4
% 0.13/0.40  # Initial clauses in saturation        : 52
% 0.13/0.40  # Processed clauses                    : 433
% 0.13/0.40  # ...of these trivial                  : 48
% 0.13/0.40  # ...subsumed                          : 38
% 0.13/0.40  # ...remaining for further processing  : 347
% 0.13/0.40  # Other redundant clauses eliminated   : 6
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 178
% 0.13/0.40  # Generated clauses                    : 641
% 0.13/0.40  # ...of the previous two non-trivial   : 537
% 0.13/0.40  # Contextual simplify-reflections      : 17
% 0.13/0.40  # Paramodulations                      : 635
% 0.13/0.40  # Factorizations                       : 0
% 0.13/0.40  # Equation resolutions                 : 6
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 109
% 0.13/0.40  #    Positive orientable unit clauses  : 41
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 0
% 0.13/0.40  #    Non-unit-clauses                  : 68
% 0.13/0.40  # Current number of unprocessed clauses: 171
% 0.13/0.40  # ...number of literals in the above   : 588
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 232
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1931
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 841
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 58
% 0.13/0.40  # Unit Clause-clause subsumption calls : 1301
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 68
% 0.13/0.40  # BW rewrite match successes           : 28
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 14313
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.055 s
% 0.13/0.40  # System time              : 0.005 s
% 0.13/0.40  # Total time               : 0.060 s
% 0.13/0.40  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
