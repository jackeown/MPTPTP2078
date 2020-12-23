%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  140 (2836 expanded)
%              Number of clauses        :   92 (1119 expanded)
%              Number of leaves         :   24 ( 717 expanded)
%              Depth                    :   14
%              Number of atoms          :  428 (12773 expanded)
%              Number of equality atoms :   79 (1778 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc6_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X2))
         => v5_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc4_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v2_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(cc1_partfun1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

fof(rc1_relset_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_xboole_0(X3)
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_24,negated_conjecture,(
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

fof(c_0_25,plain,(
    ! [X53] :
      ( ( v1_funct_1(X53)
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) )
      & ( m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))
        | ~ v1_relat_1(X53)
        | ~ v1_funct_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_26,plain,(
    ! [X31] :
      ( ( k2_relat_1(X31) = k1_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) )
      & ( k1_relat_1(X31) = k2_relat_1(k2_funct_1(X31))
        | ~ v2_funct_1(X31)
        | ~ v1_relat_1(X31)
        | ~ v1_funct_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_27,plain,(
    ! [X28] :
      ( ( v1_relat_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) )
      & ( v1_funct_1(k2_funct_1(X28))
        | ~ v1_relat_1(X28)
        | ~ v1_funct_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_28,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k2_relset_1(X41,X42,X43) = k2_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_29,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v2_funct_1(esk5_0)
    & k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0
    & ( ~ v1_funct_1(k2_funct_1(esk5_0))
      | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_30,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | v1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_31,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_37])).

cnf(c_0_48,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_42])).

fof(c_0_51,plain,(
    ! [X54,X55,X56,X57] :
      ( ( v1_funct_1(X57)
        | X55 = k1_xboole_0
        | ~ r1_tarski(X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v1_funct_2(X57,X54,X56)
        | X55 = k1_xboole_0
        | ~ r1_tarski(X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X56)))
        | X55 = k1_xboole_0
        | ~ r1_tarski(X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v1_funct_1(X57)
        | X54 != k1_xboole_0
        | ~ r1_tarski(X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v1_funct_2(X57,X54,X56)
        | X54 != k1_xboole_0
        | ~ r1_tarski(X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X56)))
        | X54 != k1_xboole_0
        | ~ r1_tarski(X55,X56)
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_53,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_44]),c_0_45]),c_0_46]),c_0_47])])).

fof(c_0_55,plain,(
    ! [X35,X36,X37] :
      ( ( v4_relat_1(X37,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v5_relat_1(X37,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_56,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ v5_relat_1(X16,X15)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X16))
      | v5_relat_1(X17,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_58,plain,(
    ! [X20,X21] :
      ( ( ~ v5_relat_1(X21,X20)
        | r1_tarski(k2_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_tarski(k2_relat_1(X21),X20)
        | v5_relat_1(X21,X20)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_59,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_53]),c_0_45]),c_0_46]),c_0_47])])).

fof(c_0_62,plain,(
    ! [X18,X19] :
      ( ( ~ v4_relat_1(X19,X18)
        | r1_tarski(k1_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k1_relat_1(X19),X18)
        | v4_relat_1(X19,X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_63,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_64,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_65,plain,
    ( v5_relat_1(X3,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_44]),c_0_46]),c_0_47])])).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_57])).

cnf(c_0_68,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_37])).

cnf(c_0_73,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_74,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_75,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_76,negated_conjecture,
    ( v5_relat_1(esk5_0,X1)
    | ~ v5_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_77,plain,
    ( v5_relat_1(X1,k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_50])).

cnf(c_0_78,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ v1_relat_1(esk5_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_46])])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_35]),c_0_46]),c_0_47])])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_47])])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( v4_relat_1(k2_zfmisc_1(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_57])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

fof(c_0_87,plain,(
    ! [X29] :
      ( v1_relat_1(k6_relat_1(X29))
      & v2_funct_1(k6_relat_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[fc4_funct_1])).

fof(c_0_88,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_funct_1(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
      | v1_funct_1(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_89,plain,(
    ! [X38,X39,X40] :
      ( ~ v1_xboole_0(X38)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | v1_xboole_0(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_90,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_91,negated_conjecture,
    ( v5_relat_1(esk5_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_67])])).

cnf(c_0_92,plain,
    ( v5_relat_1(k2_zfmisc_1(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_57])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_60]),c_0_61])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_47])])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

fof(c_0_96,plain,(
    ! [X25] :
      ( ( k1_relat_1(X25) != k1_xboole_0
        | k2_relat_1(X25) = k1_xboole_0
        | ~ v1_relat_1(X25) )
      & ( k2_relat_1(X25) != k1_xboole_0
        | k1_relat_1(X25) = k1_xboole_0
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_97,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_85]),c_0_67])])).

cnf(c_0_99,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_100,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_101,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_102,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_103,plain,(
    ! [X47,X48,X49] :
      ( ~ v1_xboole_0(X47)
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))
      | v1_partfun1(X49,X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).

cnf(c_0_104,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

fof(c_0_105,plain,(
    ! [X50,X51] :
      ( m1_subset_1(esk2_2(X50,X51),k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      & v1_xboole_0(esk2_2(X50,X51))
      & v1_relat_1(esk2_2(X50,X51))
      & v4_relat_1(esk2_2(X50,X51),X50)
      & v5_relat_1(esk2_2(X50,X51),X51) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(esk4_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_44]),c_0_47])])).

cnf(c_0_107,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_92]),c_0_67])])).

cnf(c_0_108,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ r1_tarski(k1_relat_1(esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_35]),c_0_46]),c_0_47])])).

cnf(c_0_109,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_110,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

cnf(c_0_111,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_112,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

fof(c_0_113,plain,(
    ! [X24] :
      ( ( k1_relat_1(X24) != k1_xboole_0
        | X24 = k1_xboole_0
        | ~ v1_relat_1(X24) )
      & ( k2_relat_1(X24) != k1_xboole_0
        | X24 = k1_xboole_0
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_114,plain,(
    ! [X44,X45,X46] :
      ( ( v1_funct_1(X46)
        | ~ v1_funct_1(X46)
        | ~ v1_partfun1(X46,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(X46,X44,X45)
        | ~ v1_funct_1(X46)
        | ~ v1_partfun1(X46,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_115,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_74])).

cnf(c_0_116,plain,
    ( v1_partfun1(X2,X1)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_117,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_104,c_0_74])).

cnf(c_0_118,plain,
    ( v1_xboole_0(esk2_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_105])).

cnf(c_0_119,negated_conjecture,
    ( k2_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_106]),c_0_107])])).

cnf(c_0_120,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_82]),c_0_109])).

cnf(c_0_121,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_112])])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_66])).

cnf(c_0_123,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_124,plain,
    ( v2_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_125,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_114])).

cnf(c_0_126,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_46]),c_0_47])])).

cnf(c_0_127,plain,
    ( v1_partfun1(k2_zfmisc_1(X1,X2),X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_116,c_0_57])).

cnf(c_0_128,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_129,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120]),c_0_99]),c_0_121])).

cnf(c_0_130,negated_conjecture,
    ( k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_83,c_0_122])).

cnf(c_0_131,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_53]),c_0_34])).

cnf(c_0_132,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_101])).

cnf(c_0_133,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_74]),c_0_126])])).

cnf(c_0_134,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_99]),c_0_128])])).

cnf(c_0_135,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk5_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_129]),c_0_129]),c_0_99])).

cnf(c_0_136,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_120]),c_0_99]),c_0_120]),c_0_99]),c_0_84])])).

cnf(c_0_137,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_111]),c_0_132]),c_0_126]),c_0_112])])).

cnf(c_0_138,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_139,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135,c_0_136]),c_0_137]),c_0_138]),c_0_136]),c_0_137]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:17:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.42  # and selection function SelectNewComplexAHPNS.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.42  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.42  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.42  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.42  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(t9_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 0.19/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.42  fof(cc6_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(X2))=>v5_relat_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 0.19/0.42  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.42  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.42  fof(fc4_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v2_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 0.19/0.42  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.19/0.42  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.19/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.42  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.42  fof(cc1_partfun1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_partfun1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 0.19/0.42  fof(rc1_relset_1, axiom, ![X1, X2]:?[X3]:((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_xboole_0(X3))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relset_1)).
% 0.19/0.42  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.42  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.42  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.19/0.42  fof(c_0_25, plain, ![X53]:(((v1_funct_1(X53)|(~v1_relat_1(X53)|~v1_funct_1(X53)))&(v1_funct_2(X53,k1_relat_1(X53),k2_relat_1(X53))|(~v1_relat_1(X53)|~v1_funct_1(X53))))&(m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X53),k2_relat_1(X53))))|(~v1_relat_1(X53)|~v1_funct_1(X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.42  fof(c_0_26, plain, ![X31]:((k2_relat_1(X31)=k1_relat_1(k2_funct_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))&(k1_relat_1(X31)=k2_relat_1(k2_funct_1(X31))|~v2_funct_1(X31)|(~v1_relat_1(X31)|~v1_funct_1(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.42  fof(c_0_27, plain, ![X28]:((v1_relat_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))&(v1_funct_1(k2_funct_1(X28))|(~v1_relat_1(X28)|~v1_funct_1(X28)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.42  fof(c_0_28, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k2_relset_1(X41,X42,X43)=k2_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.42  fof(c_0_29, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v2_funct_1(esk5_0)&k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0)&(~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.19/0.42  fof(c_0_30, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.42  fof(c_0_31, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  cnf(c_0_32, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  cnf(c_0_33, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_34, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_35, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_36, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.42  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_40, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.42  fof(c_0_41, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_43, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.42  cnf(c_0_44, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_39, c_0_37])).
% 0.19/0.42  cnf(c_0_48, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_33]), c_0_34]), c_0_35])).
% 0.19/0.42  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_42])).
% 0.19/0.42  fof(c_0_51, plain, ![X54, X55, X56, X57]:((((v1_funct_1(X57)|X55=k1_xboole_0|~r1_tarski(X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&(v1_funct_2(X57,X54,X56)|X55=k1_xboole_0|~r1_tarski(X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&(m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X56)))|X55=k1_xboole_0|~r1_tarski(X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&(((v1_funct_1(X57)|X54!=k1_xboole_0|~r1_tarski(X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&(v1_funct_2(X57,X54,X56)|X54!=k1_xboole_0|~r1_tarski(X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&(m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X56)))|X54!=k1_xboole_0|~r1_tarski(X55,X56)|(~v1_funct_1(X57)|~v1_funct_2(X57,X54,X55)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).
% 0.19/0.42  cnf(c_0_52, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_53, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.42  cnf(c_0_54, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_44]), c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.42  fof(c_0_55, plain, ![X35, X36, X37]:((v4_relat_1(X37,X35)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(v5_relat_1(X37,X36)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.42  fof(c_0_56, plain, ![X15, X16, X17]:(~v1_relat_1(X16)|~v5_relat_1(X16,X15)|(~m1_subset_1(X17,k1_zfmisc_1(X16))|v5_relat_1(X17,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_relat_1])])])).
% 0.19/0.42  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.42  fof(c_0_58, plain, ![X20, X21]:((~v5_relat_1(X21,X20)|r1_tarski(k2_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_tarski(k2_relat_1(X21),X20)|v5_relat_1(X21,X20)|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.42  cnf(c_0_59, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_53]), c_0_45]), c_0_46]), c_0_47])])).
% 0.19/0.42  fof(c_0_62, plain, ![X18, X19]:((~v4_relat_1(X19,X18)|r1_tarski(k1_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_tarski(k1_relat_1(X19),X18)|v4_relat_1(X19,X18)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.42  cnf(c_0_63, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  fof(c_0_64, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.42  cnf(c_0_65, plain, (v5_relat_1(X3,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_44]), c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_67, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_39, c_0_57])).
% 0.19/0.42  cnf(c_0_68, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.42  cnf(c_0_69, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)|~v1_funct_1(k2_funct_1(esk5_0))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61])])).
% 0.19/0.42  cnf(c_0_71, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_63, c_0_37])).
% 0.19/0.42  cnf(c_0_73, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.42  cnf(c_0_74, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.42  fof(c_0_75, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (v5_relat_1(esk5_0,X1)|~v5_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 0.19/0.42  cnf(c_0_77, plain, (v5_relat_1(X1,k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_50])).
% 0.19/0.42  cnf(c_0_78, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.42  cnf(c_0_79, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~v1_relat_1(esk5_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_35]), c_0_46])])).
% 0.19/0.42  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_35]), c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_47])])).
% 0.19/0.42  cnf(c_0_83, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.42  cnf(c_0_84, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.42  cnf(c_0_85, plain, (v4_relat_1(k2_zfmisc_1(X1,X2),X1)), inference(spm,[status(thm)],[c_0_63, c_0_57])).
% 0.19/0.42  cnf(c_0_86, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.42  fof(c_0_87, plain, ![X29]:(v1_relat_1(k6_relat_1(X29))&v2_funct_1(k6_relat_1(X29))), inference(variable_rename,[status(thm)],[fc4_funct_1])).
% 0.19/0.42  fof(c_0_88, plain, ![X26, X27]:(~v1_relat_1(X26)|~v1_funct_1(X26)|(~m1_subset_1(X27,k1_zfmisc_1(X26))|v1_funct_1(X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.19/0.42  fof(c_0_89, plain, ![X38, X39, X40]:(~v1_xboole_0(X38)|(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_xboole_0(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.19/0.42  cnf(c_0_90, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (v5_relat_1(esk5_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_67])])).
% 0.19/0.42  cnf(c_0_92, plain, (v5_relat_1(k2_zfmisc_1(X1,X2),X2)), inference(spm,[status(thm)],[c_0_78, c_0_57])).
% 0.19/0.42  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~v1_funct_1(k2_funct_1(esk5_0))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_60]), c_0_61])])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_47])])).
% 0.19/0.42  cnf(c_0_95, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.42  fof(c_0_96, plain, ![X25]:((k1_relat_1(X25)!=k1_xboole_0|k2_relat_1(X25)=k1_xboole_0|~v1_relat_1(X25))&(k2_relat_1(X25)!=k1_xboole_0|k1_relat_1(X25)=k1_xboole_0|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.42  cnf(c_0_97, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.19/0.42  cnf(c_0_98, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_85]), c_0_67])])).
% 0.19/0.42  cnf(c_0_99, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_86])).
% 0.19/0.42  cnf(c_0_100, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.42  cnf(c_0_101, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.42  cnf(c_0_102, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.42  fof(c_0_103, plain, ![X47, X48, X49]:(~v1_xboole_0(X47)|(~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48)))|v1_partfun1(X49,X47))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_partfun1])])])).
% 0.19/0.42  cnf(c_0_104, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.19/0.42  fof(c_0_105, plain, ![X50, X51]:((((m1_subset_1(esk2_2(X50,X51),k1_zfmisc_1(k2_zfmisc_1(X50,X51)))&v1_xboole_0(esk2_2(X50,X51)))&v1_relat_1(esk2_2(X50,X51)))&v4_relat_1(esk2_2(X50,X51),X50))&v5_relat_1(esk2_2(X50,X51),X51)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_relset_1])])).
% 0.19/0.42  cnf(c_0_106, negated_conjecture, (r1_tarski(esk4_0,k2_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_44]), c_0_47])])).
% 0.19/0.42  cnf(c_0_107, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_92]), c_0_67])])).
% 0.19/0.42  cnf(c_0_108, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~r1_tarski(k1_relat_1(esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_35]), c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_109, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.42  cnf(c_0_110, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.42  cnf(c_0_111, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.19/0.42  cnf(c_0_112, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.42  fof(c_0_113, plain, ![X24]:((k1_relat_1(X24)!=k1_xboole_0|X24=k1_xboole_0|~v1_relat_1(X24))&(k2_relat_1(X24)!=k1_xboole_0|X24=k1_xboole_0|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.42  fof(c_0_114, plain, ![X44, X45, X46]:((v1_funct_1(X46)|(~v1_funct_1(X46)|~v1_partfun1(X46,X44))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(v1_funct_2(X46,X44,X45)|(~v1_funct_1(X46)|~v1_partfun1(X46,X44))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.42  cnf(c_0_115, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_102, c_0_74])).
% 0.19/0.42  cnf(c_0_116, plain, (v1_partfun1(X2,X1)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.19/0.42  cnf(c_0_117, plain, (v1_xboole_0(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_104, c_0_74])).
% 0.19/0.42  cnf(c_0_118, plain, (v1_xboole_0(esk2_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_105])).
% 0.19/0.42  cnf(c_0_119, negated_conjecture, (k2_relat_1(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_106]), c_0_107])])).
% 0.19/0.42  cnf(c_0_120, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_82]), c_0_109])).
% 0.19/0.42  cnf(c_0_121, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_111]), c_0_112])])).
% 0.19/0.42  cnf(c_0_122, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0))), inference(spm,[status(thm)],[c_0_73, c_0_66])).
% 0.19/0.42  cnf(c_0_123, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.19/0.42  cnf(c_0_124, plain, (v2_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.42  cnf(c_0_125, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_114])).
% 0.19/0.42  cnf(c_0_126, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_46]), c_0_47])])).
% 0.19/0.42  cnf(c_0_127, plain, (v1_partfun1(k2_zfmisc_1(X1,X2),X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_116, c_0_57])).
% 0.19/0.42  cnf(c_0_128, plain, (v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 0.19/0.42  cnf(c_0_129, negated_conjecture, (esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120]), c_0_99]), c_0_121])).
% 0.19/0.42  cnf(c_0_130, negated_conjecture, (k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0)=esk5_0|~r1_tarski(k2_zfmisc_1(k1_relat_1(esk5_0),esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_83, c_0_122])).
% 0.19/0.42  cnf(c_0_131, plain, (k2_funct_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_53]), c_0_34])).
% 0.19/0.42  cnf(c_0_132, plain, (v2_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_124, c_0_101])).
% 0.19/0.42  cnf(c_0_133, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_74]), c_0_126])])).
% 0.19/0.42  cnf(c_0_134, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_99]), c_0_128])])).
% 0.19/0.42  cnf(c_0_135, negated_conjecture, (~v1_funct_2(k2_funct_1(esk5_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_129]), c_0_129]), c_0_99])).
% 0.19/0.42  cnf(c_0_136, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_120]), c_0_99]), c_0_120]), c_0_99]), c_0_84])])).
% 0.19/0.42  cnf(c_0_137, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_111]), c_0_132]), c_0_126]), c_0_112])])).
% 0.19/0.42  cnf(c_0_138, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_133, c_0_134])).
% 0.19/0.42  cnf(c_0_139, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_135, c_0_136]), c_0_137]), c_0_138]), c_0_136]), c_0_137]), c_0_74])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 140
% 0.19/0.42  # Proof object clause steps            : 92
% 0.19/0.42  # Proof object formula steps           : 48
% 0.19/0.42  # Proof object conjectures             : 37
% 0.19/0.42  # Proof object clause conjectures      : 34
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 37
% 0.19/0.42  # Proof object initial formulas used   : 24
% 0.19/0.42  # Proof object generating inferences   : 48
% 0.19/0.42  # Proof object simplifying inferences  : 89
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 27
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 59
% 0.19/0.42  # Removed in clause preprocessing      : 4
% 0.19/0.42  # Initial clauses in saturation        : 55
% 0.19/0.42  # Processed clauses                    : 617
% 0.19/0.42  # ...of these trivial                  : 10
% 0.19/0.42  # ...subsumed                          : 107
% 0.19/0.42  # ...remaining for further processing  : 500
% 0.19/0.42  # Other redundant clauses eliminated   : 6
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 7
% 0.19/0.42  # Backward-rewritten                   : 198
% 0.19/0.42  # Generated clauses                    : 1746
% 0.19/0.42  # ...of the previous two non-trivial   : 1111
% 0.19/0.42  # Contextual simplify-reflections      : 18
% 0.19/0.42  # Paramodulations                      : 1740
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 6
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 236
% 0.19/0.42  #    Positive orientable unit clauses  : 105
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 0
% 0.19/0.42  #    Non-unit-clauses                  : 131
% 0.19/0.42  # Current number of unprocessed clauses: 552
% 0.19/0.42  # ...number of literals in the above   : 1439
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 258
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 7117
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 3729
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 130
% 0.19/0.42  # Unit Clause-clause subsumption calls : 598
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 188
% 0.19/0.42  # BW rewrite match successes           : 21
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 30754
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.078 s
% 0.19/0.42  # System time              : 0.007 s
% 0.19/0.42  # Total time               : 0.086 s
% 0.19/0.42  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
