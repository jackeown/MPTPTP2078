%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:48 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 910 expanded)
%              Number of clauses        :   71 ( 349 expanded)
%              Number of leaves         :   21 ( 268 expanded)
%              Depth                    :   17
%              Number of atoms          :  286 (1677 expanded)
%              Number of equality atoms :   95 ( 870 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t44_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k7_relset_1(X1,X2,X4,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_2)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t13_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
     => ( r1_tarski(k1_relat_1(X4),X2)
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

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

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,k1_tarski(esk3_0),esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))
    & esk4_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk3_0),esk4_0,esk6_0,esk5_0),k1_tarski(k1_funct_1(esk6_0,esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_23,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_24,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_25,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_26,plain,(
    ! [X31,X32,X33,X34] : k3_enumset1(X31,X31,X32,X33,X34) = k2_enumset1(X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_27,plain,(
    ! [X35,X36,X37,X38,X39] : k4_enumset1(X35,X35,X36,X37,X38,X39) = k3_enumset1(X35,X36,X37,X38,X39) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_28,plain,(
    ! [X40,X41,X42,X43,X44,X45] : k5_enumset1(X40,X40,X41,X42,X43,X44,X45) = k4_enumset1(X40,X41,X42,X43,X44,X45) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_29,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] : k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52) = k5_enumset1(X46,X47,X48,X49,X50,X51,X52) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk3_0),esk4_0,esk6_0,esk5_0),k1_tarski(k1_funct_1(esk6_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X73,X74,X75,X76] :
      ( ~ m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))
      | k7_relset_1(X73,X74,X75,X76) = k9_relat_1(X75,X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_40,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk6_0,esk5_0),k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_41,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

fof(c_0_43,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X62)
      | ~ v1_funct_1(X62)
      | k1_relat_1(X62) != k1_tarski(X61)
      | k2_relat_1(X62) = k1_tarski(k1_funct_1(X62,X61)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_44,plain,(
    ! [X63,X64,X65] :
      ( ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))
      | v1_relat_1(X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk6_0,esk5_0),k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_46,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_47,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k7_relset_1(X1,X2,esk6_0,esk5_0),k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_41])).

cnf(c_0_49,plain,
    ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_31]),c_0_31]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36]),c_0_37]),c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_42])).

fof(c_0_52,plain,(
    ! [X82,X83,X84,X85] :
      ( ~ v1_funct_1(X85)
      | ~ v1_funct_2(X85,X82,X83)
      | ~ m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))
      | r1_tarski(k7_relset_1(X82,X83,X85,X84),X83) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_2])])).

cnf(c_0_53,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != k1_relat_1(esk6_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k7_relset_1(X1,X2,esk6_0,esk5_0),k2_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_54,plain,
    ( r1_tarski(k7_relset_1(X2,X3,X1,X4),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_55,plain,(
    ! [X81] :
      ( ( v1_funct_1(X81)
        | ~ v1_relat_1(X81)
        | ~ v1_funct_1(X81) )
      & ( v1_funct_2(X81,k1_relat_1(X81),k2_relat_1(X81))
        | ~ v1_relat_1(X81)
        | ~ v1_funct_1(X81) )
      & ( m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X81),k2_relat_1(X81))))
        | ~ v1_relat_1(X81)
        | ~ v1_funct_1(X81) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_56,plain,(
    ! [X66,X67,X68] :
      ( ( v4_relat_1(X68,X66)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) )
      & ( v5_relat_1(X68,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_57,plain,(
    ! [X57,X58] :
      ( ( ~ m1_subset_1(X57,k1_zfmisc_1(X58))
        | r1_tarski(X57,X58) )
      & ( ~ r1_tarski(X57,X58)
        | m1_subset_1(X57,k1_zfmisc_1(X58)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_58,plain,(
    ! [X53,X54] :
      ( ( k2_zfmisc_1(X53,X54) != k1_xboole_0
        | X53 = k1_xboole_0
        | X54 = k1_xboole_0 )
      & ( X53 != k1_xboole_0
        | k2_zfmisc_1(X53,X54) = k1_xboole_0 )
      & ( X54 != k1_xboole_0
        | k2_zfmisc_1(X53,X54) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_59,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != k1_relat_1(esk6_0)
    | ~ v1_funct_2(esk6_0,X1,k2_relat_1(esk6_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_50])])).

cnf(c_0_60,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_61,plain,(
    ! [X16,X17,X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X19,X18)
        | X19 = X16
        | X19 = X17
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X16
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( X20 != X17
        | r2_hidden(X20,X18)
        | X18 != k2_tarski(X16,X17) )
      & ( esk2_3(X21,X22,X23) != X21
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( esk2_3(X21,X22,X23) != X22
        | ~ r2_hidden(esk2_3(X21,X22,X23),X23)
        | X23 = k2_tarski(X21,X22) )
      & ( r2_hidden(esk2_3(X21,X22,X23),X23)
        | esk2_3(X21,X22,X23) = X21
        | esk2_3(X21,X22,X23) = X22
        | X23 = k2_tarski(X21,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_62,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != k1_relat_1(esk6_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk6_0),k2_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_50]),c_0_51])])).

cnf(c_0_67,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_68,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X3)
    | esk2_3(X1,X2,X3) = X1
    | esk2_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

fof(c_0_69,plain,(
    ! [X77,X78,X79,X80] :
      ( ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X79)))
      | ~ r1_tarski(k1_relat_1(X80),X78)
      | m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).

fof(c_0_70,plain,(
    ! [X59,X60] :
      ( ( ~ v4_relat_1(X60,X59)
        | r1_tarski(k1_relat_1(X60),X59)
        | ~ v1_relat_1(X60) )
      & ( ~ r1_tarski(k1_relat_1(X60),X59)
        | v4_relat_1(X60,X59)
        | ~ v1_relat_1(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_71,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_72,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_73,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_63])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_65])).

fof(c_0_75,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_76,negated_conjecture,
    ( k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0) != k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_50]),c_0_51])])).

cnf(c_0_77,plain,
    ( esk2_3(X1,X2,X3) = X2
    | esk2_3(X1,X2,X3) = X1
    | X3 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_78,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k1_relat_1(X1),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,plain,
    ( v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_82,plain,(
    ! [X69,X70,X71,X72] :
      ( ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | m1_subset_1(k7_relset_1(X69,X70,X71,X72),k1_zfmisc_1(X70)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_83,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_84,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_85,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)) = esk3_0
    | r2_hidden(esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( v4_relat_1(esk6_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_42])).

cnf(c_0_87,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_78,c_0_74])).

cnf(c_0_88,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_90,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_91,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_92,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_93,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)) = esk3_0
    | r2_hidden(esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)),X1)
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_86]),c_0_51])])).

cnf(c_0_95,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_63]),c_0_88])).

cnf(c_0_96,plain,
    ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_97,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_84,c_0_91])).

cnf(c_0_98,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_99,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)) = esk3_0
    | r2_hidden(esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))
    | ~ r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_42])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_95])).

cnf(c_0_103,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( r2_hidden(esk1_2(k1_relat_1(esk6_0),X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))
    | r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_97,c_0_94])).

cnf(c_0_105,plain,
    ( X3 = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)
    | esk2_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_106,negated_conjecture,
    ( esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)) = esk3_0 ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),esk4_0)))
    | ~ r1_tarski(k1_relat_1(esk6_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_103,c_0_74])).

cnf(c_0_109,negated_conjecture,
    ( esk1_2(k1_relat_1(esk6_0),X1) = esk3_0
    | r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_104])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(esk3_0,k1_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_76])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk6_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_74]),c_0_74]),c_0_108])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_109]),c_0_110])).

cnf(c_0_113,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n021.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 21:04:49 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.18/0.31  # No SInE strategy applied
% 0.18/0.31  # Trying AutoSched0 for 299 seconds
% 0.18/0.57  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.57  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.57  #
% 0.18/0.57  # Preprocessing time       : 0.014 s
% 0.18/0.57  # Presaturation interreduction done
% 0.18/0.57  
% 0.18/0.57  # Proof found!
% 0.18/0.57  # SZS status Theorem
% 0.18/0.57  # SZS output start CNFRefutation
% 0.18/0.57  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 0.18/0.57  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.18/0.57  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.18/0.57  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.18/0.57  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 0.18/0.57  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 0.18/0.57  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 0.18/0.57  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 0.18/0.57  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.18/0.57  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 0.18/0.57  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.57  fof(t44_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k7_relset_1(X1,X2,X4,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_2)).
% 0.18/0.57  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.18/0.57  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.57  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.57  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.57  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.18/0.57  fof(t13_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))=>(r1_tarski(k1_relat_1(X4),X2)=>m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 0.18/0.57  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.18/0.57  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.57  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.18/0.57  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.18/0.57  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,k1_tarski(esk3_0),esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0))))&(esk4_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk3_0),esk4_0,esk6_0,esk5_0),k1_tarski(k1_funct_1(esk6_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.18/0.57  fof(c_0_23, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.18/0.57  fof(c_0_24, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.18/0.57  fof(c_0_25, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.18/0.57  fof(c_0_26, plain, ![X31, X32, X33, X34]:k3_enumset1(X31,X31,X32,X33,X34)=k2_enumset1(X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.18/0.57  fof(c_0_27, plain, ![X35, X36, X37, X38, X39]:k4_enumset1(X35,X35,X36,X37,X38,X39)=k3_enumset1(X35,X36,X37,X38,X39), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.18/0.57  fof(c_0_28, plain, ![X40, X41, X42, X43, X44, X45]:k5_enumset1(X40,X40,X41,X42,X43,X44,X45)=k4_enumset1(X40,X41,X42,X43,X44,X45), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.18/0.57  fof(c_0_29, plain, ![X46, X47, X48, X49, X50, X51, X52]:k6_enumset1(X46,X46,X47,X48,X49,X50,X51,X52)=k5_enumset1(X46,X47,X48,X49,X50,X51,X52), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.18/0.57  cnf(c_0_30, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk3_0),esk4_0,esk6_0,esk5_0),k1_tarski(k1_funct_1(esk6_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.57  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.57  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.57  cnf(c_0_33, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.18/0.57  cnf(c_0_34, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.18/0.57  cnf(c_0_35, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.57  cnf(c_0_36, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.57  cnf(c_0_37, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.18/0.57  fof(c_0_38, plain, ![X73, X74, X75, X76]:(~m1_subset_1(X75,k1_zfmisc_1(k2_zfmisc_1(X73,X74)))|k7_relset_1(X73,X74,X75,X76)=k9_relat_1(X75,X76)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.18/0.57  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk3_0),esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.57  cnf(c_0_40, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0,esk6_0,esk5_0),k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.18/0.57  cnf(c_0_41, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.57  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0),esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.57  fof(c_0_43, plain, ![X61, X62]:(~v1_relat_1(X62)|~v1_funct_1(X62)|(k1_relat_1(X62)!=k1_tarski(X61)|k2_relat_1(X62)=k1_tarski(k1_funct_1(X62,X61)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.18/0.57  fof(c_0_44, plain, ![X63, X64, X65]:(~m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(X63,X64)))|v1_relat_1(X65)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.57  cnf(c_0_45, negated_conjecture, (~r1_tarski(k9_relat_1(esk6_0,esk5_0),k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.18/0.57  cnf(c_0_46, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.18/0.57  cnf(c_0_47, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.57  cnf(c_0_48, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k7_relset_1(X1,X2,esk6_0,esk5_0),k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0)))), inference(spm,[status(thm)],[c_0_45, c_0_41])).
% 0.18/0.57  cnf(c_0_49, plain, (k2_relat_1(X1)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_31]), c_0_31]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36]), c_0_37]), c_0_37])).
% 0.18/0.57  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.57  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 0.18/0.57  fof(c_0_52, plain, ![X82, X83, X84, X85]:(~v1_funct_1(X85)|~v1_funct_2(X85,X82,X83)|~m1_subset_1(X85,k1_zfmisc_1(k2_zfmisc_1(X82,X83)))|r1_tarski(k7_relset_1(X82,X83,X85,X84),X83)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_funct_2])])).
% 0.18/0.57  cnf(c_0_53, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk6_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_tarski(k7_relset_1(X1,X2,esk6_0,esk5_0),k2_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51])])).
% 0.18/0.57  cnf(c_0_54, plain, (r1_tarski(k7_relset_1(X2,X3,X1,X4),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.18/0.57  fof(c_0_55, plain, ![X81]:(((v1_funct_1(X81)|(~v1_relat_1(X81)|~v1_funct_1(X81)))&(v1_funct_2(X81,k1_relat_1(X81),k2_relat_1(X81))|(~v1_relat_1(X81)|~v1_funct_1(X81))))&(m1_subset_1(X81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X81),k2_relat_1(X81))))|(~v1_relat_1(X81)|~v1_funct_1(X81)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.18/0.57  fof(c_0_56, plain, ![X66, X67, X68]:((v4_relat_1(X68,X66)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))&(v5_relat_1(X68,X67)|~m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.57  fof(c_0_57, plain, ![X57, X58]:((~m1_subset_1(X57,k1_zfmisc_1(X58))|r1_tarski(X57,X58))&(~r1_tarski(X57,X58)|m1_subset_1(X57,k1_zfmisc_1(X58)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.57  fof(c_0_58, plain, ![X53, X54]:((k2_zfmisc_1(X53,X54)!=k1_xboole_0|(X53=k1_xboole_0|X54=k1_xboole_0))&((X53!=k1_xboole_0|k2_zfmisc_1(X53,X54)=k1_xboole_0)&(X54!=k1_xboole_0|k2_zfmisc_1(X53,X54)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.57  cnf(c_0_59, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk6_0)|~v1_funct_2(esk6_0,X1,k2_relat_1(esk6_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_50])])).
% 0.18/0.57  cnf(c_0_60, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.57  fof(c_0_61, plain, ![X16, X17, X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X19,X18)|(X19=X16|X19=X17)|X18!=k2_tarski(X16,X17))&((X20!=X16|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))&(X20!=X17|r2_hidden(X20,X18)|X18!=k2_tarski(X16,X17))))&(((esk2_3(X21,X22,X23)!=X21|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22))&(esk2_3(X21,X22,X23)!=X22|~r2_hidden(esk2_3(X21,X22,X23),X23)|X23=k2_tarski(X21,X22)))&(r2_hidden(esk2_3(X21,X22,X23),X23)|(esk2_3(X21,X22,X23)=X21|esk2_3(X21,X22,X23)=X22)|X23=k2_tarski(X21,X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.18/0.57  cnf(c_0_62, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.18/0.57  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.57  cnf(c_0_64, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.57  cnf(c_0_65, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.57  cnf(c_0_66, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk6_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk6_0),k2_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_50]), c_0_51])])).
% 0.18/0.57  cnf(c_0_67, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.57  cnf(c_0_68, plain, (r2_hidden(esk2_3(X1,X2,X3),X3)|esk2_3(X1,X2,X3)=X1|esk2_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.57  fof(c_0_69, plain, ![X77, X78, X79, X80]:(~m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X77,X79)))|(~r1_tarski(k1_relat_1(X80),X78)|m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(X78,X79))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_relset_1])])).
% 0.18/0.57  fof(c_0_70, plain, ![X59, X60]:((~v4_relat_1(X60,X59)|r1_tarski(k1_relat_1(X60),X59)|~v1_relat_1(X60))&(~r1_tarski(k1_relat_1(X60),X59)|v4_relat_1(X60,X59)|~v1_relat_1(X60))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.18/0.57  cnf(c_0_71, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.18/0.57  cnf(c_0_72, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_64])).
% 0.18/0.57  cnf(c_0_73, plain, (v1_relat_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_47, c_0_63])).
% 0.18/0.57  cnf(c_0_74, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_65])).
% 0.18/0.57  fof(c_0_75, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.57  cnf(c_0_76, negated_conjecture, (k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0)!=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_50]), c_0_51])])).
% 0.18/0.57  cnf(c_0_77, plain, (esk2_3(X1,X2,X3)=X2|esk2_3(X1,X2,X3)=X1|X3=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)|r2_hidden(esk2_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.57  cnf(c_0_78, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k1_relat_1(X1),X4)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.18/0.57  cnf(c_0_79, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.18/0.57  cnf(c_0_80, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.18/0.57  cnf(c_0_81, plain, (v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.18/0.57  fof(c_0_82, plain, ![X69, X70, X71, X72]:(~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|m1_subset_1(k7_relset_1(X69,X70,X71,X72),k1_zfmisc_1(X70))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.18/0.57  cnf(c_0_83, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.57  cnf(c_0_84, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.18/0.57  cnf(c_0_85, negated_conjecture, (esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0))=esk3_0|r2_hidden(esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)),k1_relat_1(esk6_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77])])).
% 0.18/0.57  cnf(c_0_86, negated_conjecture, (v4_relat_1(esk6_0,k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_62, c_0_42])).
% 0.18/0.57  cnf(c_0_87, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_78, c_0_74])).
% 0.18/0.57  cnf(c_0_88, plain, (r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.18/0.57  cnf(c_0_89, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.18/0.57  cnf(c_0_90, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.18/0.57  cnf(c_0_91, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.18/0.57  cnf(c_0_92, plain, (X1=X4|X1=X3|X2!=k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.57  cnf(c_0_93, negated_conjecture, (esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0))=esk3_0|r2_hidden(esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)),X1)|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.18/0.57  cnf(c_0_94, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_86]), c_0_51])])).
% 0.18/0.57  cnf(c_0_95, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_63]), c_0_88])).
% 0.18/0.57  cnf(c_0_96, plain, (r1_tarski(k7_relset_1(X1,X2,X3,X4),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.18/0.57  cnf(c_0_97, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_84, c_0_91])).
% 0.18/0.57  cnf(c_0_98, plain, (X3=k2_tarski(X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.57  cnf(c_0_99, plain, (X1=X2|X1=X3|~r2_hidden(X1,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_92])).
% 0.18/0.57  cnf(c_0_100, negated_conjecture, (esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0))=esk3_0|r2_hidden(esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0)),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 0.18/0.57  cnf(c_0_101, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk4_0)))|~r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_78, c_0_42])).
% 0.18/0.57  cnf(c_0_102, plain, (r1_tarski(X1,k2_zfmisc_1(X2,X3))|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_89, c_0_95])).
% 0.18/0.57  cnf(c_0_103, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,k6_enumset1(k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0),k1_funct_1(esk6_0,esk3_0)))))), inference(spm,[status(thm)],[c_0_48, c_0_96])).
% 0.18/0.57  cnf(c_0_104, negated_conjecture, (r2_hidden(esk1_2(k1_relat_1(esk6_0),X1),k6_enumset1(esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0,esk3_0))|r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_97, c_0_94])).
% 0.18/0.57  cnf(c_0_105, plain, (X3=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)|esk2_3(X1,X2,X3)!=X2|~r2_hidden(esk2_3(X1,X2,X3),X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])).
% 0.18/0.57  cnf(c_0_106, negated_conjecture, (esk2_3(esk3_0,esk3_0,k1_relat_1(esk6_0))=esk3_0), inference(spm,[status(thm)],[c_0_99, c_0_100])).
% 0.18/0.57  cnf(c_0_107, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),esk4_0)))|~r1_tarski(k1_relat_1(esk6_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 0.18/0.57  cnf(c_0_108, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_103, c_0_74])).
% 0.18/0.57  cnf(c_0_109, negated_conjecture, (esk1_2(k1_relat_1(esk6_0),X1)=esk3_0|r1_tarski(k1_relat_1(esk6_0),X1)), inference(spm,[status(thm)],[c_0_99, c_0_104])).
% 0.18/0.57  cnf(c_0_110, negated_conjecture, (~r2_hidden(esk3_0,k1_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_76])).
% 0.18/0.57  cnf(c_0_111, negated_conjecture, (~r1_tarski(k1_relat_1(esk6_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_74]), c_0_74]), c_0_108])).
% 0.18/0.57  cnf(c_0_112, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_109]), c_0_110])).
% 0.18/0.57  cnf(c_0_113, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112])]), ['proof']).
% 0.18/0.57  # SZS output end CNFRefutation
% 0.18/0.57  # Proof object total steps             : 114
% 0.18/0.57  # Proof object clause steps            : 71
% 0.18/0.57  # Proof object formula steps           : 43
% 0.18/0.57  # Proof object conjectures             : 31
% 0.18/0.57  # Proof object clause conjectures      : 28
% 0.18/0.57  # Proof object formula conjectures     : 3
% 0.18/0.57  # Proof object initial clauses used    : 29
% 0.18/0.57  # Proof object initial formulas used   : 21
% 0.18/0.57  # Proof object generating inferences   : 32
% 0.18/0.57  # Proof object simplifying inferences  : 80
% 0.18/0.57  # Training examples: 0 positive, 0 negative
% 0.18/0.57  # Parsed axioms                        : 23
% 0.18/0.57  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.57  # Initial clauses                      : 43
% 0.18/0.57  # Removed in clause preprocessing      : 8
% 0.18/0.57  # Initial clauses in saturation        : 35
% 0.18/0.57  # Processed clauses                    : 1383
% 0.18/0.57  # ...of these trivial                  : 5
% 0.18/0.57  # ...subsumed                          : 888
% 0.18/0.57  # ...remaining for further processing  : 490
% 0.18/0.57  # Other redundant clauses eliminated   : 187
% 0.18/0.57  # Clauses deleted for lack of memory   : 0
% 0.18/0.57  # Backward-subsumed                    : 30
% 0.18/0.57  # Backward-rewritten                   : 30
% 0.18/0.57  # Generated clauses                    : 7459
% 0.18/0.57  # ...of the previous two non-trivial   : 6776
% 0.18/0.57  # Contextual simplify-reflections      : 9
% 0.18/0.57  # Paramodulations                      : 7244
% 0.18/0.57  # Factorizations                       : 30
% 0.18/0.57  # Equation resolutions                 : 187
% 0.18/0.57  # Propositional unsat checks           : 0
% 0.18/0.57  #    Propositional check models        : 0
% 0.18/0.57  #    Propositional check unsatisfiable : 0
% 0.18/0.57  #    Propositional clauses             : 0
% 0.18/0.57  #    Propositional clauses after purity: 0
% 0.18/0.57  #    Propositional unsat core size     : 0
% 0.18/0.57  #    Propositional preprocessing time  : 0.000
% 0.18/0.57  #    Propositional encoding time       : 0.000
% 0.18/0.57  #    Propositional solver time         : 0.000
% 0.18/0.57  #    Success case prop preproc time    : 0.000
% 0.18/0.57  #    Success case prop encoding time   : 0.000
% 0.18/0.57  #    Success case prop solver time     : 0.000
% 0.18/0.57  # Current number of processed clauses  : 389
% 0.18/0.57  #    Positive orientable unit clauses  : 43
% 0.18/0.57  #    Positive unorientable unit clauses: 0
% 0.18/0.57  #    Negative unit clauses             : 9
% 0.18/0.57  #    Non-unit-clauses                  : 337
% 0.18/0.57  # Current number of unprocessed clauses: 5396
% 0.18/0.57  # ...number of literals in the above   : 41347
% 0.18/0.57  # Current number of archived formulas  : 0
% 0.18/0.57  # Current number of archived clauses   : 101
% 0.18/0.57  # Clause-clause subsumption calls (NU) : 38666
% 0.18/0.57  # Rec. Clause-clause subsumption calls : 15451
% 0.18/0.57  # Non-unit clause-clause subsumptions  : 626
% 0.18/0.57  # Unit Clause-clause subsumption calls : 803
% 0.18/0.57  # Rewrite failures with RHS unbound    : 0
% 0.18/0.57  # BW rewrite match attempts            : 36
% 0.18/0.57  # BW rewrite match successes           : 16
% 0.18/0.57  # Condensation attempts                : 0
% 0.18/0.57  # Condensation successes               : 0
% 0.18/0.57  # Termbank termtop insertions          : 234097
% 0.18/0.57  
% 0.18/0.57  # -------------------------------------------------
% 0.18/0.57  # User time                : 0.243 s
% 0.18/0.57  # System time              : 0.014 s
% 0.18/0.57  # Total time               : 0.257 s
% 0.18/0.57  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
