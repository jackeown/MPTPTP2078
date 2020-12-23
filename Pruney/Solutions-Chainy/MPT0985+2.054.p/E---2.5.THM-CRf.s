%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  152 (2251 expanded)
%              Number of clauses        :   91 ( 868 expanded)
%              Number of leaves         :   31 ( 579 expanded)
%              Depth                    :   13
%              Number of atoms          :  437 (10189 expanded)
%              Number of equality atoms :  110 (1480 expanded)
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

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t37_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k2_relat_1(X1) = k1_relat_1(k4_relat_1(X1))
        & k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(dt_k4_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t80_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(d9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(X1) = k4_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(t53_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( ? [X2] :
            ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X1)) )
       => v2_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(c_0_31,negated_conjecture,(
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

fof(c_0_32,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k2_relset_1(X51,X52,X53) = k2_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_33,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

fof(c_0_34,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | v1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_35,plain,(
    ! [X59] :
      ( ( v1_funct_1(X59)
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( v1_funct_2(X59,k1_relat_1(X59),k2_relat_1(X59))
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) )
      & ( m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X59),k2_relat_1(X59))))
        | ~ v1_relat_1(X59)
        | ~ v1_funct_1(X59) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_36,plain,(
    ! [X42] :
      ( ( k2_relat_1(X42) = k1_relat_1(k2_funct_1(X42))
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) )
      & ( k1_relat_1(X42) = k2_relat_1(k2_funct_1(X42))
        | ~ v2_funct_1(X42)
        | ~ v1_relat_1(X42)
        | ~ v1_funct_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_37,plain,(
    ! [X34] :
      ( ( v1_relat_1(k2_funct_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( v1_funct_1(k2_funct_1(X34))
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_38,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_49,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_51,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_52,plain,(
    ! [X13] : m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_53,plain,(
    ! [X12] : k2_subset_1(X12) = X12 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_54,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k9_relat_1(X23,k1_relat_1(X23)) = k2_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_55,plain,(
    ! [X32] :
      ( ~ v1_relat_1(X32)
      | k7_relat_1(X32,k1_relat_1(X32)) = X32 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_56,plain,(
    ! [X60,X61,X62,X63] :
      ( ( v1_funct_1(X63)
        | X61 = k1_xboole_0
        | ~ r1_tarski(X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( v1_funct_2(X63,X60,X62)
        | X61 = k1_xboole_0
        | ~ r1_tarski(X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X62)))
        | X61 = k1_xboole_0
        | ~ r1_tarski(X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( v1_funct_1(X63)
        | X60 != k1_xboole_0
        | ~ r1_tarski(X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( v1_funct_2(X63,X60,X62)
        | X60 != k1_xboole_0
        | ~ r1_tarski(X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) )
      & ( m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X62)))
        | X60 != k1_xboole_0
        | ~ r1_tarski(X61,X62)
        | ~ v1_funct_1(X63)
        | ~ v1_funct_2(X63,X60,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk4_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]),c_0_49]),c_0_50])])).

cnf(c_0_59,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_43]),c_0_44]),c_0_45])).

fof(c_0_60,plain,(
    ! [X48,X49,X50] :
      ( ( v4_relat_1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v5_relat_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_61,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | ~ v1_xboole_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

fof(c_0_64,plain,(
    ! [X29] :
      ( ( k1_relat_1(X29) != k1_xboole_0
        | k2_relat_1(X29) = k1_xboole_0
        | ~ v1_relat_1(X29) )
      & ( k2_relat_1(X29) != k1_xboole_0
        | k1_relat_1(X29) = k1_xboole_0
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_65,plain,(
    ! [X24,X25] :
      ( ~ v1_relat_1(X25)
      | k2_relat_1(k7_relat_1(X25,X24)) = k9_relat_1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_66,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_67,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_47]),c_0_48]),c_0_50])])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_47]),c_0_48]),c_0_50])])).

fof(c_0_71,plain,(
    ! [X19,X20] :
      ( ( ~ v4_relat_1(X20,X19)
        | r1_tarski(k1_relat_1(X20),X19)
        | ~ v1_relat_1(X20) )
      & ( ~ r1_tarski(k1_relat_1(X20),X19)
        | v4_relat_1(X20,X19)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_72,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

fof(c_0_75,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_76,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk4_0),esk3_0) = k2_relat_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_58])).

cnf(c_0_79,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk4_0),esk3_0) = k2_funct_1(esk4_0)
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_58])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,X1)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_82,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_39])).

fof(c_0_84,plain,(
    ! [X28] :
      ( ( k1_relat_1(X28) != k1_xboole_0
        | X28 = k1_xboole_0
        | ~ v1_relat_1(X28) )
      & ( k2_relat_1(X28) != k1_xboole_0
        | X28 = k1_xboole_0
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

fof(c_0_85,plain,(
    ! [X27] :
      ( ( k2_relat_1(X27) = k1_relat_1(k4_relat_1(X27))
        | ~ v1_relat_1(X27) )
      & ( k1_relat_1(X27) = k2_relat_1(k4_relat_1(X27))
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).

fof(c_0_86,plain,(
    ! [X21] :
      ( ~ v1_relat_1(X21)
      | v1_relat_1(k4_relat_1(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).

fof(c_0_87,plain,(
    ! [X30] :
      ( k1_relat_1(k6_relat_1(X30)) = X30
      & k2_relat_1(k6_relat_1(X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_88,plain,(
    ! [X35] :
      ( v1_relat_1(k6_relat_1(X35))
      & v1_funct_1(k6_relat_1(X35)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_89,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_90,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_91,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k1_xboole_0
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( k9_relat_1(k2_funct_1(esk4_0),esk3_0) = k2_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_44]),c_0_48]),c_0_50])])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(k2_funct_1(esk4_0),esk3_0) = k2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_44]),c_0_48]),c_0_50])])).

cnf(c_0_94,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_relat_1(esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_45]),c_0_48])])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,X1)
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_45]),c_0_48]),c_0_50])])).

cnf(c_0_97,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_50])])).

cnf(c_0_98,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_99,plain,
    ( k1_relat_1(X1) = k2_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_100,plain,
    ( v1_relat_1(k4_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_101,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_102,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_103,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_104,plain,(
    ! [X31] :
      ( ~ v1_relat_1(X31)
      | k5_relat_1(X31,k6_relat_1(k2_relat_1(X31))) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).

cnf(c_0_105,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

fof(c_0_106,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_107,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_108,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_109,plain,(
    ! [X57] :
      ( v1_partfun1(k6_partfun1(X57),X57)
      & m1_subset_1(k6_partfun1(X57),k1_zfmisc_1(k2_zfmisc_1(X57,X57))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_110,plain,(
    ! [X58] : k6_partfun1(X58) = k6_relat_1(X58) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_111,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k2_relat_1(k2_funct_1(esk4_0)) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93]),c_0_58]),c_0_93])])).

cnf(c_0_112,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_69]),c_0_70])])).

cnf(c_0_113,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_50])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

fof(c_0_115,plain,(
    ! [X33] :
      ( ~ v1_relat_1(X33)
      | ~ v1_funct_1(X33)
      | ~ v2_funct_1(X33)
      | k2_funct_1(X33) = k4_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).

cnf(c_0_116,plain,
    ( k4_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_100])).

cnf(c_0_117,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_118,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_102])).

cnf(c_0_119,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

fof(c_0_120,plain,(
    ! [X40,X41] :
      ( ~ v1_relat_1(X40)
      | ~ v1_funct_1(X40)
      | ~ v1_relat_1(X41)
      | ~ v1_funct_1(X41)
      | k5_relat_1(X40,X41) != k6_relat_1(k1_relat_1(X40))
      | v2_funct_1(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).

cnf(c_0_121,plain,
    ( k5_relat_1(X1,k6_relat_1(k2_relat_1(X1))) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_104])).

cnf(c_0_122,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_105,c_0_102])).

fof(c_0_123,plain,(
    ! [X54,X55,X56] :
      ( ( v1_funct_1(X56)
        | ~ v1_funct_1(X56)
        | ~ v1_partfun1(X56,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( v1_funct_2(X56,X54,X55)
        | ~ v1_funct_1(X56)
        | ~ v1_partfun1(X56,X54)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_124,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_106])).

cnf(c_0_125,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_126,plain,
    ( v1_partfun1(k6_partfun1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_109])).

cnf(c_0_127,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_128,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relat_1(esk4_0) != k1_xboole_0
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_43]),c_0_47]),c_0_48]),c_0_50])])).

cnf(c_0_129,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_69])).

cnf(c_0_130,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r1_tarski(k1_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_45]),c_0_48]),c_0_50])])).

cnf(c_0_131,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_132,plain,
    ( k2_funct_1(X1) = k4_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_115])).

cnf(c_0_133,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118])])).

cnf(c_0_134,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_119,c_0_102])).

cnf(c_0_135,plain,
    ( v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k5_relat_1(X1,X2) != k6_relat_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_120])).

cnf(c_0_136,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_102]),c_0_118])])).

cnf(c_0_137,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_123])).

cnf(c_0_138,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_124,c_0_125])).

cnf(c_0_139,plain,
    ( v1_partfun1(k6_relat_1(X1),X1) ),
    inference(rw,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_140,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_relat_1(esk4_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129])])).

cnf(c_0_141,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_97]),c_0_131])).

cnf(c_0_142,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_143,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | ~ v2_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_134]),c_0_118])])).

cnf(c_0_144,plain,
    ( v2_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135,c_0_136]),c_0_117]),c_0_102]),c_0_134]),c_0_118])])).

cnf(c_0_145,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | ~ v1_partfun1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_134])])).

cnf(c_0_146,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_139,c_0_102])).

cnf(c_0_147,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140,c_0_141])])).

cnf(c_0_148,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_141]),c_0_50])])).

cnf(c_0_149,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_143,c_0_144])])).

cnf(c_0_150,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_151,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113,c_0_147]),c_0_147]),c_0_148]),c_0_149]),c_0_150]),c_0_148]),c_0_149]),c_0_138])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:24:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.47  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.19/0.47  # and selection function SelectNewComplexAHPNS.
% 0.19/0.47  #
% 0.19/0.47  # Preprocessing time       : 0.029 s
% 0.19/0.47  # Presaturation interreduction done
% 0.19/0.47  
% 0.19/0.47  # Proof found!
% 0.19/0.47  # SZS status Theorem
% 0.19/0.47  # SZS output start CNFRefutation
% 0.19/0.47  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.47  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.47  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.47  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.47  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.47  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.19/0.47  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.47  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.47  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 0.19/0.47  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.19/0.47  fof(t9_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 0.19/0.47  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.47  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.47  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.47  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.19/0.47  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.47  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.47  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.47  fof(t37_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k4_relat_1(X1))&k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 0.19/0.47  fof(dt_k4_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>v1_relat_1(k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 0.19/0.47  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.19/0.47  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.19/0.47  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.19/0.47  fof(t80_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 0.19/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.47  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.47  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 0.19/0.47  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.19/0.47  fof(d9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(X1)=k4_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 0.19/0.47  fof(t53_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(?[X2]:((v1_relat_1(X2)&v1_funct_1(X2))&k5_relat_1(X1,X2)=k6_relat_1(k1_relat_1(X1)))=>v2_funct_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_funct_1)).
% 0.19/0.47  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.19/0.47  fof(c_0_31, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.19/0.47  fof(c_0_32, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k2_relset_1(X51,X52,X53)=k2_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.47  fof(c_0_33, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.19/0.47  fof(c_0_34, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|v1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.47  fof(c_0_35, plain, ![X59]:(((v1_funct_1(X59)|(~v1_relat_1(X59)|~v1_funct_1(X59)))&(v1_funct_2(X59,k1_relat_1(X59),k2_relat_1(X59))|(~v1_relat_1(X59)|~v1_funct_1(X59))))&(m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X59),k2_relat_1(X59))))|(~v1_relat_1(X59)|~v1_funct_1(X59)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.47  fof(c_0_36, plain, ![X42]:((k2_relat_1(X42)=k1_relat_1(k2_funct_1(X42))|~v2_funct_1(X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))&(k1_relat_1(X42)=k2_relat_1(k2_funct_1(X42))|~v2_funct_1(X42)|(~v1_relat_1(X42)|~v1_funct_1(X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.47  fof(c_0_37, plain, ![X34]:((v1_relat_1(k2_funct_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(v1_funct_1(k2_funct_1(X34))|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.19/0.47  cnf(c_0_38, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.47  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_40, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_41, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.47  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  cnf(c_0_43, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_44, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_45, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.47  cnf(c_0_46, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.47  cnf(c_0_47, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_49, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.47  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 0.19/0.47  cnf(c_0_51, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.47  fof(c_0_52, plain, ![X13]:m1_subset_1(k2_subset_1(X13),k1_zfmisc_1(X13)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.47  fof(c_0_53, plain, ![X12]:k2_subset_1(X12)=X12, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.47  fof(c_0_54, plain, ![X23]:(~v1_relat_1(X23)|k9_relat_1(X23,k1_relat_1(X23))=k2_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.19/0.47  fof(c_0_55, plain, ![X32]:(~v1_relat_1(X32)|k7_relat_1(X32,k1_relat_1(X32))=X32), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.19/0.47  fof(c_0_56, plain, ![X60, X61, X62, X63]:((((v1_funct_1(X63)|X61=k1_xboole_0|~r1_tarski(X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))))&(v1_funct_2(X63,X60,X62)|X61=k1_xboole_0|~r1_tarski(X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))))&(m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X62)))|X61=k1_xboole_0|~r1_tarski(X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))))&(((v1_funct_1(X63)|X60!=k1_xboole_0|~r1_tarski(X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61)))))&(v1_funct_2(X63,X60,X62)|X60!=k1_xboole_0|~r1_tarski(X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))))&(m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X62)))|X60!=k1_xboole_0|~r1_tarski(X61,X62)|(~v1_funct_1(X63)|~v1_funct_2(X63,X60,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X60,X61))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).
% 0.19/0.47  cnf(c_0_57, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.47  cnf(c_0_58, negated_conjecture, (k1_relat_1(k2_funct_1(esk4_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])]), c_0_49]), c_0_50])])).
% 0.19/0.47  cnf(c_0_59, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_43]), c_0_44]), c_0_45])).
% 0.19/0.47  fof(c_0_60, plain, ![X48, X49, X50]:((v4_relat_1(X50,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v5_relat_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.47  fof(c_0_61, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|~v1_xboole_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.47  cnf(c_0_62, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.47  cnf(c_0_63, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.47  fof(c_0_64, plain, ![X29]:((k1_relat_1(X29)!=k1_xboole_0|k2_relat_1(X29)=k1_xboole_0|~v1_relat_1(X29))&(k2_relat_1(X29)!=k1_xboole_0|k1_relat_1(X29)=k1_xboole_0|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.47  fof(c_0_65, plain, ![X24, X25]:(~v1_relat_1(X25)|k2_relat_1(k7_relat_1(X25,X24))=k9_relat_1(X25,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.19/0.47  cnf(c_0_66, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.47  cnf(c_0_67, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.47  cnf(c_0_68, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.47  cnf(c_0_69, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_47]), c_0_48]), c_0_50])])).
% 0.19/0.47  cnf(c_0_70, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_47]), c_0_48]), c_0_50])])).
% 0.19/0.47  fof(c_0_71, plain, ![X19, X20]:((~v4_relat_1(X20,X19)|r1_tarski(k1_relat_1(X20),X19)|~v1_relat_1(X20))&(~r1_tarski(k1_relat_1(X20),X19)|v4_relat_1(X20,X19)|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.47  cnf(c_0_72, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.47  cnf(c_0_73, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.47  cnf(c_0_74, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.47  fof(c_0_75, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.47  cnf(c_0_76, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.19/0.47  cnf(c_0_77, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.47  cnf(c_0_78, negated_conjecture, (k9_relat_1(k2_funct_1(esk4_0),esk3_0)=k2_relat_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_66, c_0_58])).
% 0.19/0.47  cnf(c_0_79, negated_conjecture, (k7_relat_1(k2_funct_1(esk4_0),esk3_0)=k2_funct_1(esk4_0)|~v1_relat_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_58])).
% 0.19/0.47  cnf(c_0_80, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.47  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,X1)|~v1_funct_1(k2_funct_1(esk4_0))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])])).
% 0.19/0.47  cnf(c_0_82, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.19/0.47  cnf(c_0_83, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_72, c_0_39])).
% 0.19/0.47  fof(c_0_84, plain, ![X28]:((k1_relat_1(X28)!=k1_xboole_0|X28=k1_xboole_0|~v1_relat_1(X28))&(k2_relat_1(X28)!=k1_xboole_0|X28=k1_xboole_0|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.47  fof(c_0_85, plain, ![X27]:((k2_relat_1(X27)=k1_relat_1(k4_relat_1(X27))|~v1_relat_1(X27))&(k1_relat_1(X27)=k2_relat_1(k4_relat_1(X27))|~v1_relat_1(X27))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_relat_1])])])).
% 0.19/0.47  fof(c_0_86, plain, ![X21]:(~v1_relat_1(X21)|v1_relat_1(k4_relat_1(X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relat_1])])).
% 0.19/0.47  fof(c_0_87, plain, ![X30]:(k1_relat_1(k6_relat_1(X30))=X30&k2_relat_1(k6_relat_1(X30))=X30), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.19/0.47  fof(c_0_88, plain, ![X35]:(v1_relat_1(k6_relat_1(X35))&v1_funct_1(k6_relat_1(X35))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.19/0.47  cnf(c_0_89, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.47  cnf(c_0_90, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.19/0.47  cnf(c_0_91, plain, (k1_relat_1(k7_relat_1(X1,X2))=k1_xboole_0|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.19/0.47  cnf(c_0_92, negated_conjecture, (k9_relat_1(k2_funct_1(esk4_0),esk3_0)=k2_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_44]), c_0_48]), c_0_50])])).
% 0.19/0.47  cnf(c_0_93, negated_conjecture, (k7_relat_1(k2_funct_1(esk4_0),esk3_0)=k2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_44]), c_0_48]), c_0_50])])).
% 0.19/0.47  cnf(c_0_94, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.47  cnf(c_0_95, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_relat_1(esk4_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_45]), c_0_48])])).
% 0.19/0.47  cnf(c_0_96, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,X1)|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_45]), c_0_48]), c_0_50])])).
% 0.19/0.47  cnf(c_0_97, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_50])])).
% 0.19/0.47  cnf(c_0_98, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.47  cnf(c_0_99, plain, (k1_relat_1(X1)=k2_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.19/0.47  cnf(c_0_100, plain, (v1_relat_1(k4_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.19/0.47  cnf(c_0_101, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.47  cnf(c_0_102, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.19/0.47  cnf(c_0_103, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.47  fof(c_0_104, plain, ![X31]:(~v1_relat_1(X31)|k5_relat_1(X31,k6_relat_1(k2_relat_1(X31)))=X31), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t80_relat_1])])).
% 0.19/0.47  cnf(c_0_105, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.19/0.47  fof(c_0_106, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.47  cnf(c_0_107, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.47  cnf(c_0_108, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.47  fof(c_0_109, plain, ![X57]:(v1_partfun1(k6_partfun1(X57),X57)&m1_subset_1(k6_partfun1(X57),k1_zfmisc_1(k2_zfmisc_1(X57,X57)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 0.19/0.47  fof(c_0_110, plain, ![X58]:k6_partfun1(X58)=k6_relat_1(X58), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.19/0.47  cnf(c_0_111, negated_conjecture, (esk3_0=k1_xboole_0|k2_relat_1(k2_funct_1(esk4_0))!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93]), c_0_58]), c_0_93])])).
% 0.19/0.47  cnf(c_0_112, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v1_funct_1(k2_funct_1(esk4_0))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_69]), c_0_70])])).
% 0.19/0.47  cnf(c_0_113, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_50])])).
% 0.19/0.47  cnf(c_0_114, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.19/0.47  fof(c_0_115, plain, ![X33]:(~v1_relat_1(X33)|~v1_funct_1(X33)|(~v2_funct_1(X33)|k2_funct_1(X33)=k4_relat_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_1])])).
% 0.19/0.47  cnf(c_0_116, plain, (k4_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_100])).
% 0.19/0.47  cnf(c_0_117, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.19/0.47  cnf(c_0_118, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_103, c_0_102])).
% 0.19/0.47  cnf(c_0_119, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.19/0.47  fof(c_0_120, plain, ![X40, X41]:(~v1_relat_1(X40)|~v1_funct_1(X40)|(~v1_relat_1(X41)|~v1_funct_1(X41)|k5_relat_1(X40,X41)!=k6_relat_1(k1_relat_1(X40))|v2_funct_1(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t53_funct_1])])])).
% 0.19/0.47  cnf(c_0_121, plain, (k5_relat_1(X1,k6_relat_1(k2_relat_1(X1)))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_104])).
% 0.19/0.47  cnf(c_0_122, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_105, c_0_102])).
% 0.19/0.47  fof(c_0_123, plain, ![X54, X55, X56]:((v1_funct_1(X56)|(~v1_funct_1(X56)|~v1_partfun1(X56,X54))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(v1_funct_2(X56,X54,X55)|(~v1_funct_1(X56)|~v1_partfun1(X56,X54))|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.19/0.47  cnf(c_0_124, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_106])).
% 0.19/0.47  cnf(c_0_125, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 0.19/0.47  cnf(c_0_126, plain, (v1_partfun1(k6_partfun1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_109])).
% 0.19/0.47  cnf(c_0_127, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.19/0.47  cnf(c_0_128, negated_conjecture, (esk3_0=k1_xboole_0|k1_relat_1(esk4_0)!=k1_xboole_0|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_43]), c_0_47]), c_0_48]), c_0_50])])).
% 0.19/0.47  cnf(c_0_129, negated_conjecture, (v1_relat_1(k2_funct_1(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_69])).
% 0.19/0.47  cnf(c_0_130, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r1_tarski(k1_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_45]), c_0_48]), c_0_50])])).
% 0.19/0.47  cnf(c_0_131, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 0.19/0.47  cnf(c_0_132, plain, (k2_funct_1(X1)=k4_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_115])).
% 0.19/0.47  cnf(c_0_133, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118])])).
% 0.19/0.47  cnf(c_0_134, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_119, c_0_102])).
% 0.19/0.47  cnf(c_0_135, plain, (v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k5_relat_1(X1,X2)!=k6_relat_1(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_120])).
% 0.19/0.47  cnf(c_0_136, plain, (k5_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_122]), c_0_102]), c_0_118])])).
% 0.19/0.47  cnf(c_0_137, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_123])).
% 0.19/0.47  cnf(c_0_138, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_124, c_0_125])).
% 0.19/0.47  cnf(c_0_139, plain, (v1_partfun1(k6_relat_1(X1),X1)), inference(rw,[status(thm)],[c_0_126, c_0_127])).
% 0.19/0.47  cnf(c_0_140, negated_conjecture, (esk3_0=k1_xboole_0|k1_relat_1(esk4_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129])])).
% 0.19/0.47  cnf(c_0_141, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_130, c_0_97]), c_0_131])).
% 0.19/0.47  cnf(c_0_142, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.47  cnf(c_0_143, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0|~v2_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_134]), c_0_118])])).
% 0.19/0.47  cnf(c_0_144, plain, (v2_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_135, c_0_136]), c_0_117]), c_0_102]), c_0_134]), c_0_118])])).
% 0.19/0.47  cnf(c_0_145, plain, (v1_funct_2(k1_xboole_0,X1,X2)|~v1_partfun1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_138]), c_0_134])])).
% 0.19/0.47  cnf(c_0_146, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_139, c_0_102])).
% 0.19/0.47  cnf(c_0_147, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_140, c_0_141])])).
% 0.19/0.47  cnf(c_0_148, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_141]), c_0_50])])).
% 0.19/0.47  cnf(c_0_149, plain, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_143, c_0_144])])).
% 0.19/0.47  cnf(c_0_150, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_145, c_0_146])).
% 0.19/0.47  cnf(c_0_151, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_113, c_0_147]), c_0_147]), c_0_148]), c_0_149]), c_0_150]), c_0_148]), c_0_149]), c_0_138])]), ['proof']).
% 0.19/0.47  # SZS output end CNFRefutation
% 0.19/0.47  # Proof object total steps             : 152
% 0.19/0.47  # Proof object clause steps            : 91
% 0.19/0.47  # Proof object formula steps           : 61
% 0.19/0.47  # Proof object conjectures             : 35
% 0.19/0.47  # Proof object clause conjectures      : 32
% 0.19/0.47  # Proof object formula conjectures     : 3
% 0.19/0.47  # Proof object initial clauses used    : 42
% 0.19/0.47  # Proof object initial formulas used   : 31
% 0.19/0.47  # Proof object generating inferences   : 42
% 0.19/0.47  # Proof object simplifying inferences  : 84
% 0.19/0.47  # Training examples: 0 positive, 0 negative
% 0.19/0.47  # Parsed axioms                        : 37
% 0.19/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.47  # Initial clauses                      : 63
% 0.19/0.47  # Removed in clause preprocessing      : 6
% 0.19/0.47  # Initial clauses in saturation        : 57
% 0.19/0.47  # Processed clauses                    : 1318
% 0.19/0.47  # ...of these trivial                  : 40
% 0.19/0.47  # ...subsumed                          : 514
% 0.19/0.47  # ...remaining for further processing  : 763
% 0.19/0.47  # Other redundant clauses eliminated   : 45
% 0.19/0.47  # Clauses deleted for lack of memory   : 0
% 0.19/0.47  # Backward-subsumed                    : 14
% 0.19/0.47  # Backward-rewritten                   : 284
% 0.19/0.47  # Generated clauses                    : 3335
% 0.19/0.47  # ...of the previous two non-trivial   : 2436
% 0.19/0.47  # Contextual simplify-reflections      : 77
% 0.19/0.47  # Paramodulations                      : 3290
% 0.19/0.47  # Factorizations                       : 0
% 0.19/0.47  # Equation resolutions                 : 45
% 0.19/0.47  # Propositional unsat checks           : 0
% 0.19/0.47  #    Propositional check models        : 0
% 0.19/0.47  #    Propositional check unsatisfiable : 0
% 0.19/0.47  #    Propositional clauses             : 0
% 0.19/0.47  #    Propositional clauses after purity: 0
% 0.19/0.47  #    Propositional unsat core size     : 0
% 0.19/0.47  #    Propositional preprocessing time  : 0.000
% 0.19/0.47  #    Propositional encoding time       : 0.000
% 0.19/0.47  #    Propositional solver time         : 0.000
% 0.19/0.47  #    Success case prop preproc time    : 0.000
% 0.19/0.47  #    Success case prop encoding time   : 0.000
% 0.19/0.47  #    Success case prop solver time     : 0.000
% 0.19/0.47  # Current number of processed clauses  : 406
% 0.19/0.47  #    Positive orientable unit clauses  : 75
% 0.19/0.47  #    Positive unorientable unit clauses: 0
% 0.19/0.47  #    Negative unit clauses             : 1
% 0.19/0.47  #    Non-unit-clauses                  : 330
% 0.19/0.47  # Current number of unprocessed clauses: 1206
% 0.19/0.47  # ...number of literals in the above   : 3907
% 0.19/0.47  # Current number of archived formulas  : 0
% 0.19/0.47  # Current number of archived clauses   : 357
% 0.19/0.47  # Clause-clause subsumption calls (NU) : 35022
% 0.19/0.47  # Rec. Clause-clause subsumption calls : 18550
% 0.19/0.47  # Non-unit clause-clause subsumptions  : 579
% 0.19/0.47  # Unit Clause-clause subsumption calls : 3516
% 0.19/0.47  # Rewrite failures with RHS unbound    : 0
% 0.19/0.47  # BW rewrite match attempts            : 160
% 0.19/0.47  # BW rewrite match successes           : 30
% 0.19/0.47  # Condensation attempts                : 0
% 0.19/0.47  # Condensation successes               : 0
% 0.19/0.47  # Termbank termtop insertions          : 55351
% 0.19/0.47  
% 0.19/0.47  # -------------------------------------------------
% 0.19/0.47  # User time                : 0.122 s
% 0.19/0.47  # System time              : 0.013 s
% 0.19/0.47  # Total time               : 0.135 s
% 0.19/0.47  # Maximum resident set size: 1620 pages
%------------------------------------------------------------------------------
