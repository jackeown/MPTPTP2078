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
% DateTime   : Thu Dec  3 11:06:06 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  151 (2590 expanded)
%              Number of clauses        :   93 ( 973 expanded)
%              Number of leaves         :   29 ( 649 expanded)
%              Depth                    :   15
%              Number of atoms          :  434 (10328 expanded)
%              Number of equality atoms :   96 ( 763 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(dt_k6_partfun1,axiom,(
    ! [X1] :
      ( v1_partfun1(k6_partfun1(X1),X1)
      & m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t88_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
        & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_funct_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v3_funct_2(X3,X1,X2) )
       => ( v1_funct_1(X3)
          & v2_funct_1(X3)
          & v2_funct_2(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(d3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1) )
     => ( v2_funct_2(X2,X1)
      <=> k2_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t61_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
          & k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(redefinition_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k2_funct_2(X1,X2) = k2_funct_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(dt_k2_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & v3_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k2_funct_2(X1,X2))
        & v1_funct_2(k2_funct_2(X1,X2),X1,X1)
        & v3_funct_2(k2_funct_2(X1,X2),X1,X1)
        & m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(t6_xboole_0,axiom,(
    ! [X1,X2] :
      ~ ( r2_xboole_0(X1,X2)
        & ! [X3] :
            ~ ( r2_hidden(X3,X2)
              & ~ r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_29,plain,(
    ! [X47] :
      ( v1_xboole_0(X47)
      | ~ v1_relat_1(X47)
      | ~ v1_xboole_0(k1_relat_1(X47)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

fof(c_0_30,plain,(
    ! [X54] :
      ( k1_relat_1(k6_relat_1(X54)) = X54
      & k2_relat_1(k6_relat_1(X54)) = X54 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_31,plain,(
    ! [X55] :
      ( v1_relat_1(k6_relat_1(X55))
      & v1_funct_1(k6_relat_1(X55)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_32,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_33,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_36,plain,(
    ! [X89] :
      ( v1_partfun1(k6_partfun1(X89),X89)
      & m1_subset_1(k6_partfun1(X89),k1_zfmisc_1(k2_zfmisc_1(X89,X89))) ) ),
    inference(variable_rename,[status(thm)],[dt_k6_partfun1])).

fof(c_0_37,plain,(
    ! [X98] : k6_partfun1(X98) = k6_relat_1(X98) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,plain,
    ( v1_xboole_0(k6_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_40,plain,(
    ! [X40,X41,X42] :
      ( ~ r2_hidden(X40,X41)
      | ~ m1_subset_1(X41,k1_zfmisc_1(X42))
      | ~ v1_xboole_0(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_41,plain,
    ( m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_43,plain,(
    ! [X30,X31] :
      ( ~ v1_xboole_0(X31)
      | v1_xboole_0(k2_zfmisc_1(X30,X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

fof(c_0_44,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & v3_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))
          & r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t88_funct_2])).

cnf(c_0_45,plain,
    ( k6_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_50,plain,(
    ! [X79,X80,X81] :
      ( ( v1_funct_1(X81)
        | ~ v1_funct_1(X81)
        | ~ v3_funct_2(X81,X79,X80)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80))) )
      & ( v2_funct_1(X81)
        | ~ v1_funct_1(X81)
        | ~ v3_funct_2(X81,X79,X80)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80))) )
      & ( v2_funct_2(X81,X80)
        | ~ v1_funct_1(X81)
        | ~ v3_funct_2(X81,X79,X80)
        | ~ m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).

fof(c_0_51,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk4_0,esk4_0)
    & v3_funct_2(esk5_0,esk4_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))
    & ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))
      | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).

fof(c_0_52,plain,(
    ! [X61,X62,X63] :
      ( ( v4_relat_1(X63,X61)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) )
      & ( v5_relat_1(X63,X62)
        | ~ m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_53,plain,(
    ! [X58,X59,X60] :
      ( ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))
      | v1_relat_1(X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_54,plain,(
    ! [X43,X44] :
      ( ( ~ v4_relat_1(X44,X43)
        | r1_tarski(k1_relat_1(X44),X43)
        | ~ v1_relat_1(X44) )
      & ( ~ r1_tarski(k1_relat_1(X44),X43)
        | v4_relat_1(X44,X43)
        | ~ v1_relat_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_55,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,k6_relat_1(X2))
    | ~ v1_xboole_0(k2_zfmisc_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_38,c_0_49])).

fof(c_0_58,plain,(
    ! [X85,X86] :
      ( ( ~ v2_funct_2(X86,X85)
        | k2_relat_1(X86) = X85
        | ~ v1_relat_1(X86)
        | ~ v5_relat_1(X86,X85) )
      & ( k2_relat_1(X86) != X85
        | v2_funct_2(X86,X85)
        | ~ v1_relat_1(X86)
        | ~ v5_relat_1(X86,X85) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).

cnf(c_0_59,plain,
    ( v2_funct_2(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( v3_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_65,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_66,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_34,c_0_55])).

cnf(c_0_67,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_55])).

fof(c_0_68,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_70,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_46])).

fof(c_0_71,plain,(
    ! [X56] :
      ( ( k5_relat_1(X56,k2_funct_1(X56)) = k6_relat_1(k1_relat_1(X56))
        | ~ v2_funct_1(X56)
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) )
      & ( k5_relat_1(k2_funct_1(X56),X56) = k6_relat_1(k2_relat_1(X56))
        | ~ v2_funct_1(X56)
        | ~ v1_relat_1(X56)
        | ~ v1_funct_1(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).

cnf(c_0_72,plain,
    ( v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v3_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_73,plain,
    ( k2_relat_1(X1) = X2
    | ~ v2_funct_2(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,negated_conjecture,
    ( v2_funct_2(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_75,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_62])).

fof(c_0_77,plain,(
    ! [X96,X97] :
      ( ~ v1_funct_1(X97)
      | ~ v1_funct_2(X97,X96,X96)
      | ~ v3_funct_2(X97,X96,X96)
      | ~ m1_subset_1(X97,k1_zfmisc_1(k2_zfmisc_1(X96,X96)))
      | k2_funct_2(X96,X97) = k2_funct_1(X97) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).

fof(c_0_78,plain,(
    ! [X49,X50] :
      ( ~ v1_relat_1(X50)
      | k2_relat_1(k7_relat_1(X50,X49)) = k9_relat_1(X50,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_79,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X52)
      | ~ v4_relat_1(X52,X51)
      | X52 = k7_relat_1(X52,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_80,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_81,plain,
    ( v4_relat_1(k1_xboole_0,X1)
    | ~ r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])])).

cnf(c_0_82,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70]),c_0_46])])).

fof(c_0_84,plain,(
    ! [X90,X91,X92,X93,X94,X95] :
      ( ~ v1_funct_1(X94)
      | ~ m1_subset_1(X94,k1_zfmisc_1(k2_zfmisc_1(X90,X91)))
      | ~ v1_funct_1(X95)
      | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X92,X93)))
      | k1_partfun1(X90,X91,X92,X93,X94,X95) = k5_relat_1(X94,X95) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_85,plain,(
    ! [X87,X88] :
      ( ( v1_funct_1(k2_funct_2(X87,X88))
        | ~ v1_funct_1(X88)
        | ~ v1_funct_2(X88,X87,X87)
        | ~ v3_funct_2(X88,X87,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87))) )
      & ( v1_funct_2(k2_funct_2(X87,X88),X87,X87)
        | ~ v1_funct_1(X88)
        | ~ v1_funct_2(X88,X87,X87)
        | ~ v3_funct_2(X88,X87,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87))) )
      & ( v3_funct_2(k2_funct_2(X87,X88),X87,X87)
        | ~ v1_funct_1(X88)
        | ~ v1_funct_2(X88,X87,X87)
        | ~ v3_funct_2(X88,X87,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87))) )
      & ( m1_subset_1(k2_funct_2(X87,X88),k1_zfmisc_1(k2_zfmisc_1(X87,X87)))
        | ~ v1_funct_1(X88)
        | ~ v1_funct_2(X88,X87,X87)
        | ~ v3_funct_2(X88,X87,X87)
        | ~ m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).

cnf(c_0_86,plain,
    ( k5_relat_1(k2_funct_1(X1),X1) = k6_relat_1(k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_87,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_88,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_76])])).

cnf(c_0_89,plain,
    ( k2_funct_2(X2,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v3_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk5_0,esk4_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_91,plain,(
    ! [X68,X69,X70,X71] :
      ( ( ~ r2_relset_1(X68,X69,X70,X71)
        | X70 = X71
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) )
      & ( X70 != X71
        | r2_relset_1(X68,X69,X70,X71)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_92,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_93,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_94,negated_conjecture,
    ( v4_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_80,c_0_62])).

fof(c_0_95,plain,(
    ! [X64,X65,X66,X67] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))
      | k7_relset_1(X64,X65,X66,X67) = k9_relat_1(X66,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_96,plain,(
    ! [X73,X74,X75] :
      ( ( k7_relset_1(X73,X74,X75,X73) = k2_relset_1(X73,X74,X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) )
      & ( k8_relset_1(X73,X74,X75,X74) = k1_relset_1(X73,X74,X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_97,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | ~ r2_xboole_0(X17,X18) )
      & ( X17 != X18
        | ~ r2_xboole_0(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | X17 = X18
        | r2_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_98,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_99,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])).

cnf(c_0_100,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_101,plain,
    ( m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_102,negated_conjecture,
    ( k5_relat_1(k2_funct_1(esk5_0),esk5_0) = k6_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_61]),c_0_76])]),c_0_88])).

cnf(c_0_103,negated_conjecture,
    ( k2_funct_1(esk5_0) = k2_funct_2(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_104,plain,
    ( v1_funct_1(k2_funct_2(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v3_funct_2(X2,X1,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_105,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_106,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

fof(c_0_107,plain,(
    ! [X99,X100,X101] :
      ( ( k5_relat_1(X101,k2_funct_1(X101)) = k6_partfun1(X99)
        | X100 = k1_xboole_0
        | k2_relset_1(X99,X100,X101) != X100
        | ~ v2_funct_1(X101)
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,X99,X100)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X99,X100))) )
      & ( k5_relat_1(k2_funct_1(X101),X101) = k6_partfun1(X100)
        | X100 = k1_xboole_0
        | k2_relset_1(X99,X100,X101) != X100
        | ~ v2_funct_1(X101)
        | ~ v1_funct_1(X101)
        | ~ v1_funct_2(X101,X99,X100)
        | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X99,X100))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

cnf(c_0_108,negated_conjecture,
    ( k2_relat_1(k7_relat_1(esk5_0,X1)) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_76])).

cnf(c_0_109,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_76])])).

cnf(c_0_110,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_111,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_112,plain,(
    ! [X20,X21] :
      ( ( r2_hidden(esk3_2(X20,X21),X21)
        | ~ r2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_2(X20,X21),X20)
        | ~ r2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).

cnf(c_0_113,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_114,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_66]),c_0_67])])).

cnf(c_0_115,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_116,negated_conjecture,
    ( k1_partfun1(X1,X2,esk4_0,esk4_0,X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_62]),c_0_61])])).

cnf(c_0_117,negated_conjecture,
    ( m1_subset_1(k2_funct_2(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_90]),c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_118,negated_conjecture,
    ( k5_relat_1(k2_funct_2(esk4_0,esk5_0),esk5_0) = k6_relat_1(esk4_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_119,negated_conjecture,
    ( v1_funct_1(k2_funct_2(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_90]),c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_120,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_105])).

cnf(c_0_121,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_1(esk5_0)) = k6_relat_1(k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_87]),c_0_61]),c_0_76])])).

cnf(c_0_122,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_123,negated_conjecture,
    ( k9_relat_1(esk5_0,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_88])).

cnf(c_0_124,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) = k7_relset_1(esk4_0,esk4_0,esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_110,c_0_62])).

cnf(c_0_125,negated_conjecture,
    ( k7_relset_1(esk4_0,esk4_0,esk5_0,esk4_0) = k2_relset_1(esk4_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_111,c_0_62])).

cnf(c_0_126,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_112])).

cnf(c_0_127,plain,
    ( k1_xboole_0 = X1
    | r2_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_113,c_0_114])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0))
    | ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_42]),c_0_42])).

cnf(c_0_129,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0) = k6_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_118]),c_0_119])])).

cnf(c_0_130,plain,
    ( r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_120,c_0_48])).

cnf(c_0_131,negated_conjecture,
    ( k1_partfun1(X1,X2,esk4_0,esk4_0,X3,k2_funct_2(esk4_0,esk5_0)) = k5_relat_1(X3,k2_funct_2(esk4_0,esk5_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_117]),c_0_119])])).

cnf(c_0_132,negated_conjecture,
    ( k5_relat_1(esk5_0,k2_funct_2(esk4_0,esk5_0)) = k6_relat_1(k1_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_121,c_0_103])).

cnf(c_0_133,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_122,c_0_42])).

cnf(c_0_134,negated_conjecture,
    ( k2_relset_1(esk4_0,esk4_0,esk5_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123,c_0_124]),c_0_125])).

cnf(c_0_135,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_62])).

cnf(c_0_136,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_137,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128,c_0_129]),c_0_130])])).

cnf(c_0_138,negated_conjecture,
    ( k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)) = k6_relat_1(k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_62]),c_0_132]),c_0_61])])).

cnf(c_0_139,negated_conjecture,
    ( k6_relat_1(k1_relat_1(esk5_0)) = k6_relat_1(esk4_0)
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_134]),c_0_103]),c_0_132]),c_0_90]),c_0_87]),c_0_61]),c_0_62])])).

fof(c_0_140,plain,(
    ! [X38,X39] :
      ( ( ~ m1_subset_1(X38,k1_zfmisc_1(X39))
        | r1_tarski(X38,X39) )
      & ( ~ r1_tarski(X38,X39)
        | m1_subset_1(X38,k1_zfmisc_1(X39)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_141,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_136])).

cnf(c_0_142,negated_conjecture,
    ( ~ r2_relset_1(esk4_0,esk4_0,k6_relat_1(k1_relat_1(esk5_0)),k6_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_137,c_0_138])).

cnf(c_0_143,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk4_0
    | esk4_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_139]),c_0_34])).

cnf(c_0_144,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_140])).

cnf(c_0_145,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | ~ v1_xboole_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_141,c_0_49])).

cnf(c_0_146,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_130])])).

cnf(c_0_147,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_144,c_0_114])).

cnf(c_0_148,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145,c_0_146]),c_0_46])])).

cnf(c_0_149,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_120,c_0_147])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_146]),c_0_146]),c_0_146]),c_0_55]),c_0_148]),c_0_66]),c_0_55]),c_0_149])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 1.94/2.13  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 1.94/2.13  # and selection function SelectCQArNTNpEqFirst.
% 1.94/2.13  #
% 1.94/2.13  # Preprocessing time       : 0.030 s
% 1.94/2.13  # Presaturation interreduction done
% 1.94/2.13  
% 1.94/2.13  # Proof found!
% 1.94/2.13  # SZS status Theorem
% 1.94/2.13  # SZS output start CNFRefutation
% 1.94/2.13  fof(fc8_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.94/2.13  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.94/2.13  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.94/2.13  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/2.13  fof(dt_k6_partfun1, axiom, ![X1]:(v1_partfun1(k6_partfun1(X1),X1)&m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 1.94/2.13  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 1.94/2.13  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.94/2.13  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 1.94/2.13  fof(t88_funct_2, conjecture, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_funct_2)).
% 1.94/2.13  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.94/2.13  fof(cc2_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v3_funct_2(X3,X1,X2))=>((v1_funct_1(X3)&v2_funct_1(X3))&v2_funct_2(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 1.94/2.13  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.94/2.13  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.94/2.13  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.94/2.13  fof(d3_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v5_relat_1(X2,X1))=>(v2_funct_2(X2,X1)<=>k2_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 1.94/2.13  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/2.13  fof(t61_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))&k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 1.94/2.13  fof(redefinition_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k2_funct_2(X1,X2)=k2_funct_1(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 1.94/2.13  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.94/2.13  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.94/2.13  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 1.94/2.13  fof(dt_k2_funct_2, axiom, ![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(((v1_funct_1(k2_funct_2(X1,X2))&v1_funct_2(k2_funct_2(X1,X2),X1,X1))&v3_funct_2(k2_funct_2(X1,X2),X1,X1))&m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 1.94/2.13  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 1.94/2.13  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.94/2.13  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 1.94/2.13  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.94/2.13  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 1.94/2.13  fof(t6_xboole_0, axiom, ![X1, X2]:~((r2_xboole_0(X1,X2)&![X3]:~((r2_hidden(X3,X2)&~(r2_hidden(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.94/2.13  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.94/2.13  fof(c_0_29, plain, ![X47]:(v1_xboole_0(X47)|~v1_relat_1(X47)|~v1_xboole_0(k1_relat_1(X47))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).
% 1.94/2.13  fof(c_0_30, plain, ![X54]:(k1_relat_1(k6_relat_1(X54))=X54&k2_relat_1(k6_relat_1(X54))=X54), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 1.94/2.13  fof(c_0_31, plain, ![X55]:(v1_relat_1(k6_relat_1(X55))&v1_funct_1(k6_relat_1(X55))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 1.94/2.13  fof(c_0_32, plain, ![X19]:(~v1_xboole_0(X19)|X19=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 1.94/2.13  cnf(c_0_33, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.94/2.13  cnf(c_0_34, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.94/2.13  cnf(c_0_35, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.94/2.13  fof(c_0_36, plain, ![X89]:(v1_partfun1(k6_partfun1(X89),X89)&m1_subset_1(k6_partfun1(X89),k1_zfmisc_1(k2_zfmisc_1(X89,X89)))), inference(variable_rename,[status(thm)],[dt_k6_partfun1])).
% 1.94/2.13  fof(c_0_37, plain, ![X98]:k6_partfun1(X98)=k6_relat_1(X98), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 1.94/2.13  cnf(c_0_38, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.94/2.13  cnf(c_0_39, plain, (v1_xboole_0(k6_relat_1(X1))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 1.94/2.13  fof(c_0_40, plain, ![X40, X41, X42]:(~r2_hidden(X40,X41)|~m1_subset_1(X41,k1_zfmisc_1(X42))|~v1_xboole_0(X42)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 1.94/2.13  cnf(c_0_41, plain, (m1_subset_1(k6_partfun1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.94/2.13  cnf(c_0_42, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.94/2.13  fof(c_0_43, plain, ![X30, X31]:(~v1_xboole_0(X31)|v1_xboole_0(k2_zfmisc_1(X30,X31))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 1.94/2.13  fof(c_0_44, negated_conjecture, ~(![X1, X2]:((((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&v3_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,X2,k2_funct_2(X1,X2)),k6_partfun1(X1))&r2_relset_1(X1,X1,k1_partfun1(X1,X1,X1,X1,k2_funct_2(X1,X2),X2),k6_partfun1(X1))))), inference(assume_negation,[status(cth)],[t88_funct_2])).
% 1.94/2.13  cnf(c_0_45, plain, (k6_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 1.94/2.13  cnf(c_0_46, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.94/2.13  cnf(c_0_47, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.94/2.13  cnf(c_0_48, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 1.94/2.13  cnf(c_0_49, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.94/2.13  fof(c_0_50, plain, ![X79, X80, X81]:(((v1_funct_1(X81)|(~v1_funct_1(X81)|~v3_funct_2(X81,X79,X80))|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80))))&(v2_funct_1(X81)|(~v1_funct_1(X81)|~v3_funct_2(X81,X79,X80))|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80)))))&(v2_funct_2(X81,X80)|(~v1_funct_1(X81)|~v3_funct_2(X81,X79,X80))|~m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(X79,X80))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_funct_2])])])).
% 1.94/2.13  fof(c_0_51, negated_conjecture, ((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk4_0,esk4_0))&v3_funct_2(esk5_0,esk4_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0))))&(~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_44])])])).
% 1.94/2.13  fof(c_0_52, plain, ![X61, X62, X63]:((v4_relat_1(X63,X61)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))&(v5_relat_1(X63,X62)|~m1_subset_1(X63,k1_zfmisc_1(k2_zfmisc_1(X61,X62))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.94/2.13  fof(c_0_53, plain, ![X58, X59, X60]:(~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))|v1_relat_1(X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.94/2.13  fof(c_0_54, plain, ![X43, X44]:((~v4_relat_1(X44,X43)|r1_tarski(k1_relat_1(X44),X43)|~v1_relat_1(X44))&(~r1_tarski(k1_relat_1(X44),X43)|v4_relat_1(X44,X43)|~v1_relat_1(X44))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.94/2.13  cnf(c_0_55, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 1.94/2.13  cnf(c_0_56, plain, (~r2_hidden(X1,k6_relat_1(X2))|~v1_xboole_0(k2_zfmisc_1(X2,X2))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 1.94/2.13  cnf(c_0_57, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_38, c_0_49])).
% 1.94/2.13  fof(c_0_58, plain, ![X85, X86]:((~v2_funct_2(X86,X85)|k2_relat_1(X86)=X85|(~v1_relat_1(X86)|~v5_relat_1(X86,X85)))&(k2_relat_1(X86)!=X85|v2_funct_2(X86,X85)|(~v1_relat_1(X86)|~v5_relat_1(X86,X85)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_funct_2])])])).
% 1.94/2.13  cnf(c_0_59, plain, (v2_funct_2(X1,X2)|~v1_funct_1(X1)|~v3_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.94/2.13  cnf(c_0_60, negated_conjecture, (v3_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.94/2.13  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.94/2.13  cnf(c_0_62, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.94/2.13  cnf(c_0_63, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.94/2.13  cnf(c_0_64, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 1.94/2.13  cnf(c_0_65, plain, (v4_relat_1(X1,X2)|~r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.94/2.13  cnf(c_0_66, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_34, c_0_55])).
% 1.94/2.13  cnf(c_0_67, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_55])).
% 1.94/2.13  fof(c_0_68, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.94/2.13  cnf(c_0_69, plain, (~r2_hidden(X1,k1_xboole_0)|~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 1.94/2.13  cnf(c_0_70, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_46])).
% 1.94/2.13  fof(c_0_71, plain, ![X56]:((k5_relat_1(X56,k2_funct_1(X56))=k6_relat_1(k1_relat_1(X56))|~v2_funct_1(X56)|(~v1_relat_1(X56)|~v1_funct_1(X56)))&(k5_relat_1(k2_funct_1(X56),X56)=k6_relat_1(k2_relat_1(X56))|~v2_funct_1(X56)|(~v1_relat_1(X56)|~v1_funct_1(X56)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_funct_1])])])).
% 1.94/2.13  cnf(c_0_72, plain, (v2_funct_1(X1)|~v1_funct_1(X1)|~v3_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 1.94/2.13  cnf(c_0_73, plain, (k2_relat_1(X1)=X2|~v2_funct_2(X1,X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 1.94/2.13  cnf(c_0_74, negated_conjecture, (v2_funct_2(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])])).
% 1.94/2.13  cnf(c_0_75, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_63, c_0_62])).
% 1.94/2.13  cnf(c_0_76, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_64, c_0_62])).
% 1.94/2.13  fof(c_0_77, plain, ![X96, X97]:(~v1_funct_1(X97)|~v1_funct_2(X97,X96,X96)|~v3_funct_2(X97,X96,X96)|~m1_subset_1(X97,k1_zfmisc_1(k2_zfmisc_1(X96,X96)))|k2_funct_2(X96,X97)=k2_funct_1(X97)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_funct_2])])).
% 1.94/2.13  fof(c_0_78, plain, ![X49, X50]:(~v1_relat_1(X50)|k2_relat_1(k7_relat_1(X50,X49))=k9_relat_1(X50,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 1.94/2.13  fof(c_0_79, plain, ![X51, X52]:(~v1_relat_1(X52)|~v4_relat_1(X52,X51)|X52=k7_relat_1(X52,X51)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 1.94/2.13  cnf(c_0_80, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.94/2.13  cnf(c_0_81, plain, (v4_relat_1(k1_xboole_0,X1)|~r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])])).
% 1.94/2.13  cnf(c_0_82, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 1.94/2.13  cnf(c_0_83, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70]), c_0_46])])).
% 1.94/2.13  fof(c_0_84, plain, ![X90, X91, X92, X93, X94, X95]:(~v1_funct_1(X94)|~m1_subset_1(X94,k1_zfmisc_1(k2_zfmisc_1(X90,X91)))|~v1_funct_1(X95)|~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(X92,X93)))|k1_partfun1(X90,X91,X92,X93,X94,X95)=k5_relat_1(X94,X95)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 1.94/2.13  fof(c_0_85, plain, ![X87, X88]:((((v1_funct_1(k2_funct_2(X87,X88))|(~v1_funct_1(X88)|~v1_funct_2(X88,X87,X87)|~v3_funct_2(X88,X87,X87)|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87)))))&(v1_funct_2(k2_funct_2(X87,X88),X87,X87)|(~v1_funct_1(X88)|~v1_funct_2(X88,X87,X87)|~v3_funct_2(X88,X87,X87)|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87))))))&(v3_funct_2(k2_funct_2(X87,X88),X87,X87)|(~v1_funct_1(X88)|~v1_funct_2(X88,X87,X87)|~v3_funct_2(X88,X87,X87)|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87))))))&(m1_subset_1(k2_funct_2(X87,X88),k1_zfmisc_1(k2_zfmisc_1(X87,X87)))|(~v1_funct_1(X88)|~v1_funct_2(X88,X87,X87)|~v3_funct_2(X88,X87,X87)|~m1_subset_1(X88,k1_zfmisc_1(k2_zfmisc_1(X87,X87)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_2])])])).
% 1.94/2.13  cnf(c_0_86, plain, (k5_relat_1(k2_funct_1(X1),X1)=k6_relat_1(k2_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.94/2.13  cnf(c_0_87, negated_conjecture, (v2_funct_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_60]), c_0_61]), c_0_62])])).
% 1.94/2.13  cnf(c_0_88, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_76])])).
% 1.94/2.13  cnf(c_0_89, plain, (k2_funct_2(X2,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~v3_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 1.94/2.13  cnf(c_0_90, negated_conjecture, (v1_funct_2(esk5_0,esk4_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.94/2.13  fof(c_0_91, plain, ![X68, X69, X70, X71]:((~r2_relset_1(X68,X69,X70,X71)|X70=X71|(~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))&(X70!=X71|r2_relset_1(X68,X69,X70,X71)|(~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X68,X69)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 1.94/2.13  cnf(c_0_92, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 1.94/2.13  cnf(c_0_93, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.94/2.13  cnf(c_0_94, negated_conjecture, (v4_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_80, c_0_62])).
% 1.94/2.13  fof(c_0_95, plain, ![X64, X65, X66, X67]:(~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(X64,X65)))|k7_relset_1(X64,X65,X66,X67)=k9_relat_1(X66,X67)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 1.94/2.13  fof(c_0_96, plain, ![X73, X74, X75]:((k7_relset_1(X73,X74,X75,X73)=k2_relset_1(X73,X74,X75)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))&(k8_relset_1(X73,X74,X75,X74)=k1_relset_1(X73,X74,X75)|~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 1.94/2.13  fof(c_0_97, plain, ![X17, X18]:(((r1_tarski(X17,X18)|~r2_xboole_0(X17,X18))&(X17!=X18|~r2_xboole_0(X17,X18)))&(~r1_tarski(X17,X18)|X17=X18|r2_xboole_0(X17,X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 1.94/2.13  cnf(c_0_98, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.94/2.13  cnf(c_0_99, plain, (v4_relat_1(k1_xboole_0,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])).
% 1.94/2.13  cnf(c_0_100, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 1.94/2.13  cnf(c_0_101, plain, (m1_subset_1(k2_funct_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.94/2.13  cnf(c_0_102, negated_conjecture, (k5_relat_1(k2_funct_1(esk5_0),esk5_0)=k6_relat_1(esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_61]), c_0_76])]), c_0_88])).
% 1.94/2.13  cnf(c_0_103, negated_conjecture, (k2_funct_1(esk5_0)=k2_funct_2(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_60]), c_0_61]), c_0_62])])).
% 1.94/2.13  cnf(c_0_104, plain, (v1_funct_1(k2_funct_2(X1,X2))|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X1)|~v3_funct_2(X2,X1,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_85])).
% 1.94/2.13  cnf(c_0_105, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 1.94/2.13  cnf(c_0_106, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(k1_relat_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 1.94/2.13  fof(c_0_107, plain, ![X99, X100, X101]:((k5_relat_1(X101,k2_funct_1(X101))=k6_partfun1(X99)|X100=k1_xboole_0|(k2_relset_1(X99,X100,X101)!=X100|~v2_funct_1(X101))|(~v1_funct_1(X101)|~v1_funct_2(X101,X99,X100)|~m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X99,X100)))))&(k5_relat_1(k2_funct_1(X101),X101)=k6_partfun1(X100)|X100=k1_xboole_0|(k2_relset_1(X99,X100,X101)!=X100|~v2_funct_1(X101))|(~v1_funct_1(X101)|~v1_funct_2(X101,X99,X100)|~m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X99,X100)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 1.94/2.13  cnf(c_0_108, negated_conjecture, (k2_relat_1(k7_relat_1(esk5_0,X1))=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_92, c_0_76])).
% 1.94/2.13  cnf(c_0_109, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_76])])).
% 1.94/2.13  cnf(c_0_110, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 1.94/2.13  cnf(c_0_111, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_96])).
% 1.94/2.13  fof(c_0_112, plain, ![X20, X21]:((r2_hidden(esk3_2(X20,X21),X21)|~r2_xboole_0(X20,X21))&(~r2_hidden(esk3_2(X20,X21),X20)|~r2_xboole_0(X20,X21))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_xboole_0])])])])])).
% 1.94/2.13  cnf(c_0_113, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_97])).
% 1.94/2.13  cnf(c_0_114, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_66]), c_0_67])])).
% 1.94/2.13  cnf(c_0_115, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_partfun1(esk4_0))|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_partfun1(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.94/2.13  cnf(c_0_116, negated_conjecture, (k1_partfun1(X1,X2,esk4_0,esk4_0,X3,esk5_0)=k5_relat_1(X3,esk5_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_62]), c_0_61])])).
% 1.94/2.13  cnf(c_0_117, negated_conjecture, (m1_subset_1(k2_funct_2(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_90]), c_0_60]), c_0_61]), c_0_62])])).
% 1.94/2.13  cnf(c_0_118, negated_conjecture, (k5_relat_1(k2_funct_2(esk4_0,esk5_0),esk5_0)=k6_relat_1(esk4_0)), inference(rw,[status(thm)],[c_0_102, c_0_103])).
% 1.94/2.13  cnf(c_0_119, negated_conjecture, (v1_funct_1(k2_funct_2(esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_90]), c_0_60]), c_0_61]), c_0_62])])).
% 1.94/2.13  cnf(c_0_120, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_105])).
% 1.94/2.13  cnf(c_0_121, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_1(esk5_0))=k6_relat_1(k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_87]), c_0_61]), c_0_76])])).
% 1.94/2.13  cnf(c_0_122, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_107])).
% 1.94/2.13  cnf(c_0_123, negated_conjecture, (k9_relat_1(esk5_0,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_88])).
% 1.94/2.13  cnf(c_0_124, negated_conjecture, (k9_relat_1(esk5_0,X1)=k7_relset_1(esk4_0,esk4_0,esk5_0,X1)), inference(spm,[status(thm)],[c_0_110, c_0_62])).
% 1.94/2.13  cnf(c_0_125, negated_conjecture, (k7_relset_1(esk4_0,esk4_0,esk5_0,esk4_0)=k2_relset_1(esk4_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_111, c_0_62])).
% 1.94/2.13  cnf(c_0_126, plain, (r2_hidden(esk3_2(X1,X2),X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_112])).
% 1.94/2.13  cnf(c_0_127, plain, (k1_xboole_0=X1|r2_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_113, c_0_114])).
% 1.94/2.13  cnf(c_0_128, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0))|~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0),k6_relat_1(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_42]), c_0_42])).
% 1.94/2.13  cnf(c_0_129, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,k2_funct_2(esk4_0,esk5_0),esk5_0)=k6_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_118]), c_0_119])])).
% 1.94/2.13  cnf(c_0_130, plain, (r2_relset_1(X1,X1,k6_relat_1(X1),k6_relat_1(X1))), inference(spm,[status(thm)],[c_0_120, c_0_48])).
% 1.94/2.13  cnf(c_0_131, negated_conjecture, (k1_partfun1(X1,X2,esk4_0,esk4_0,X3,k2_funct_2(esk4_0,esk5_0))=k5_relat_1(X3,k2_funct_2(esk4_0,esk5_0))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_117]), c_0_119])])).
% 1.94/2.13  cnf(c_0_132, negated_conjecture, (k5_relat_1(esk5_0,k2_funct_2(esk4_0,esk5_0))=k6_relat_1(k1_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_121, c_0_103])).
% 1.94/2.13  cnf(c_0_133, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_122, c_0_42])).
% 1.94/2.13  cnf(c_0_134, negated_conjecture, (k2_relset_1(esk4_0,esk4_0,esk5_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_123, c_0_124]), c_0_125])).
% 1.94/2.13  cnf(c_0_135, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_47, c_0_62])).
% 1.94/2.13  cnf(c_0_136, plain, (k1_xboole_0=X1|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 1.94/2.13  cnf(c_0_137, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0)),k6_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_128, c_0_129]), c_0_130])])).
% 1.94/2.13  cnf(c_0_138, negated_conjecture, (k1_partfun1(esk4_0,esk4_0,esk4_0,esk4_0,esk5_0,k2_funct_2(esk4_0,esk5_0))=k6_relat_1(k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_62]), c_0_132]), c_0_61])])).
% 1.94/2.13  cnf(c_0_139, negated_conjecture, (k6_relat_1(k1_relat_1(esk5_0))=k6_relat_1(esk4_0)|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133, c_0_134]), c_0_103]), c_0_132]), c_0_90]), c_0_87]), c_0_61]), c_0_62])])).
% 1.94/2.13  fof(c_0_140, plain, ![X38, X39]:((~m1_subset_1(X38,k1_zfmisc_1(X39))|r1_tarski(X38,X39))&(~r1_tarski(X38,X39)|m1_subset_1(X38,k1_zfmisc_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.94/2.13  cnf(c_0_141, negated_conjecture, (esk5_0=k1_xboole_0|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_135, c_0_136])).
% 1.94/2.13  cnf(c_0_142, negated_conjecture, (~r2_relset_1(esk4_0,esk4_0,k6_relat_1(k1_relat_1(esk5_0)),k6_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_137, c_0_138])).
% 1.94/2.13  cnf(c_0_143, negated_conjecture, (k1_relat_1(esk5_0)=esk4_0|esk4_0=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_139]), c_0_34])).
% 1.94/2.13  cnf(c_0_144, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_140])).
% 1.94/2.13  cnf(c_0_145, negated_conjecture, (esk5_0=k1_xboole_0|~v1_xboole_0(esk4_0)), inference(spm,[status(thm)],[c_0_141, c_0_49])).
% 1.94/2.13  cnf(c_0_146, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_130])])).
% 1.94/2.13  cnf(c_0_147, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_144, c_0_114])).
% 1.94/2.13  cnf(c_0_148, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_145, c_0_146]), c_0_46])])).
% 1.94/2.13  cnf(c_0_149, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_120, c_0_147])).
% 1.94/2.13  cnf(c_0_150, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_146]), c_0_146]), c_0_146]), c_0_55]), c_0_148]), c_0_66]), c_0_55]), c_0_149])]), ['proof']).
% 1.94/2.13  # SZS output end CNFRefutation
% 1.94/2.13  # Proof object total steps             : 151
% 1.94/2.13  # Proof object clause steps            : 93
% 1.94/2.13  # Proof object formula steps           : 58
% 1.94/2.13  # Proof object conjectures             : 42
% 1.94/2.13  # Proof object clause conjectures      : 39
% 1.94/2.13  # Proof object formula conjectures     : 3
% 1.94/2.13  # Proof object initial clauses used    : 38
% 1.94/2.13  # Proof object initial formulas used   : 29
% 1.94/2.13  # Proof object generating inferences   : 43
% 1.94/2.13  # Proof object simplifying inferences  : 87
% 1.94/2.13  # Training examples: 0 positive, 0 negative
% 1.94/2.13  # Parsed axioms                        : 45
% 1.94/2.13  # Removed by relevancy pruning/SinE    : 0
% 1.94/2.13  # Initial clauses                      : 81
% 1.94/2.13  # Removed in clause preprocessing      : 2
% 1.94/2.13  # Initial clauses in saturation        : 79
% 1.94/2.13  # Processed clauses                    : 9415
% 1.94/2.13  # ...of these trivial                  : 53
% 1.94/2.13  # ...subsumed                          : 4888
% 1.94/2.13  # ...remaining for further processing  : 4473
% 1.94/2.13  # Other redundant clauses eliminated   : 10
% 1.94/2.13  # Clauses deleted for lack of memory   : 0
% 1.94/2.13  # Backward-subsumed                    : 105
% 1.94/2.13  # Backward-rewritten                   : 2695
% 1.94/2.13  # Generated clauses                    : 227636
% 1.94/2.13  # ...of the previous two non-trivial   : 227388
% 1.94/2.13  # Contextual simplify-reflections      : 13
% 1.94/2.13  # Paramodulations                      : 227395
% 1.94/2.13  # Factorizations                       : 232
% 1.94/2.13  # Equation resolutions                 : 10
% 1.94/2.13  # Propositional unsat checks           : 0
% 1.94/2.13  #    Propositional check models        : 0
% 1.94/2.13  #    Propositional check unsatisfiable : 0
% 1.94/2.13  #    Propositional clauses             : 0
% 1.94/2.13  #    Propositional clauses after purity: 0
% 1.94/2.13  #    Propositional unsat core size     : 0
% 1.94/2.13  #    Propositional preprocessing time  : 0.000
% 1.94/2.13  #    Propositional encoding time       : 0.000
% 1.94/2.13  #    Propositional solver time         : 0.000
% 1.94/2.13  #    Success case prop preproc time    : 0.000
% 1.94/2.13  #    Success case prop encoding time   : 0.000
% 1.94/2.13  #    Success case prop solver time     : 0.000
% 1.94/2.13  # Current number of processed clauses  : 1588
% 1.94/2.13  #    Positive orientable unit clauses  : 60
% 1.94/2.13  #    Positive unorientable unit clauses: 2
% 1.94/2.13  #    Negative unit clauses             : 2
% 1.94/2.13  #    Non-unit-clauses                  : 1524
% 1.94/2.13  # Current number of unprocessed clauses: 217801
% 1.94/2.13  # ...number of literals in the above   : 684402
% 1.94/2.13  # Current number of archived formulas  : 0
% 1.94/2.13  # Current number of archived clauses   : 2879
% 1.94/2.13  # Clause-clause subsumption calls (NU) : 2996387
% 1.94/2.13  # Rec. Clause-clause subsumption calls : 2152680
% 1.94/2.13  # Non-unit clause-clause subsumptions  : 4979
% 1.94/2.13  # Unit Clause-clause subsumption calls : 26765
% 1.94/2.13  # Rewrite failures with RHS unbound    : 0
% 1.94/2.13  # BW rewrite match attempts            : 443
% 1.94/2.13  # BW rewrite match successes           : 40
% 1.94/2.13  # Condensation attempts                : 0
% 1.94/2.13  # Condensation successes               : 0
% 1.94/2.13  # Termbank termtop insertions          : 3083939
% 1.94/2.14  
% 1.94/2.14  # -------------------------------------------------
% 1.94/2.14  # User time                : 1.680 s
% 1.94/2.14  # System time              : 0.108 s
% 1.94/2.14  # Total time               : 1.788 s
% 1.94/2.14  # Maximum resident set size: 1636 pages
%------------------------------------------------------------------------------
