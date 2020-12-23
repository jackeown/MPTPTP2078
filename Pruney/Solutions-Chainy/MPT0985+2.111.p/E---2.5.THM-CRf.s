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
% DateTime   : Thu Dec  3 11:02:48 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  158 (3868 expanded)
%              Number of clauses        :  120 (1545 expanded)
%              Number of leaves         :   19 ( 960 expanded)
%              Depth                    :   22
%              Number of atoms          :  468 (17717 expanded)
%              Number of equality atoms :  166 (3344 expanded)
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t167_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(t169_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

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
    ! [X39] :
      ( ( v1_funct_1(X39)
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( v1_funct_2(X39,k1_relat_1(X39),k2_relat_1(X39))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) )
      & ( m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X39),k2_relat_1(X39))))
        | ~ v1_relat_1(X39)
        | ~ v1_funct_1(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_21,plain,(
    ! [X26] :
      ( ( k2_relat_1(X26) = k1_relat_1(k2_funct_1(X26))
        | ~ v2_funct_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( k1_relat_1(X26) = k2_relat_1(k2_funct_1(X26))
        | ~ v2_funct_1(X26)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_22,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_relset_1(X33,X34,X35) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v2_funct_1(esk4_0)
    & k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0
    & ( ~ v1_funct_1(k2_funct_1(esk4_0))
      | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_24,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk2_0,esk3_0,esk4_0) = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_31,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | k1_relset_1(X30,X31,X32) = k1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_32,plain,(
    ! [X15] : m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_33,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_34,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_30,c_0_28])).

fof(c_0_39,plain,(
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

cnf(c_0_40,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_41,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | ~ v1_xboole_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_42,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k2_relat_1(k2_funct_1(esk4_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_46,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(pm,[status(thm)],[c_0_40,c_0_28])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_52,plain,(
    ! [X4,X5,X6,X7,X8] :
      ( ( ~ r1_tarski(X4,X5)
        | ~ r2_hidden(X6,X4)
        | r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_2(X7,X8),X7)
        | r1_tarski(X7,X8) )
      & ( ~ r2_hidden(esk1_2(X7,X8),X8)
        | r1_tarski(X7,X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45,c_0_46]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_28]),c_0_48]),c_0_49])])).

fof(c_0_57,plain,(
    ! [X10,X11] :
      ( ( r1_tarski(X10,X11)
        | X10 != X11 )
      & ( r1_tarski(X11,X10)
        | X10 != X11 )
      & ( ~ r1_tarski(X10,X11)
        | ~ r1_tarski(X11,X10)
        | X10 = X11 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_58,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(pm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_60,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_61,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_64,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_63,c_0_54])).

fof(c_0_69,plain,(
    ! [X25] :
      ( ( v1_relat_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( v1_funct_1(k2_funct_1(X25))
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_70,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ r1_tarski(X2,X1) ),
    inference(pm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(pm,[status(thm)],[c_0_66,c_0_28])).

cnf(c_0_72,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_63,c_0_26])).

cnf(c_0_73,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_74,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

fof(c_0_75,plain,(
    ! [X24] :
      ( ( k1_relat_1(X24) != k1_xboole_0
        | k2_relat_1(X24) = k1_xboole_0
        | ~ v1_relat_1(X24) )
      & ( k2_relat_1(X24) != k1_xboole_0
        | k1_relat_1(X24) = k1_xboole_0
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_76,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(pm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_78,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(k2_funct_1(esk4_0)))))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_35]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_79,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_80,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk4_0)) != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_74]),c_0_37]),c_0_38])])).

fof(c_0_82,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).

cnf(c_0_83,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_84,plain,
    ( k1_relset_1(X1,X2,k2_zfmisc_1(X1,X2)) = k1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_40,c_0_51])).

cnf(c_0_85,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76,c_0_54]),c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_28,c_0_54])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78,c_0_46]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_88,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79,c_0_28]),c_0_48]),c_0_49])])).

cnf(c_0_89,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ r1_tarski(k2_funct_1(esk4_0),k2_zfmisc_1(esk3_0,esk2_0)) ),
    inference(pm,[status(thm)],[c_0_53,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(esk4_0) != k1_xboole_0
    | esk2_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_46]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_91,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_92,plain,
    ( r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83,c_0_38]),c_0_35])).

fof(c_0_94,plain,(
    ! [X23] :
      ( ~ v1_relat_1(X23)
      | k10_relat_1(X23,k2_relat_1(X23)) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).

cnf(c_0_95,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0)) = k1_relat_1(esk4_0)
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84,c_0_85]),c_0_48])).

cnf(c_0_96,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_30,c_0_51])).

cnf(c_0_97,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_86]),c_0_77])])).

cnf(c_0_98,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_89,c_0_65])).

cnf(c_0_100,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_70,c_0_65])).

cnf(c_0_101,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_102,negated_conjecture,
    ( k1_relat_1(esk4_0) != k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90,c_0_91]),c_0_37]),c_0_38])])).

cnf(c_0_103,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(pm,[status(thm)],[c_0_50,c_0_80])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk4_0,X1),k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_93]),c_0_38])])).

cnf(c_0_105,plain,
    ( k10_relat_1(X1,k2_relat_1(X1)) = k1_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( r1_tarski(k10_relat_1(k2_zfmisc_1(esk2_0,esk3_0),X1),k1_relat_1(esk4_0))
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92,c_0_95]),c_0_96])])).

cnf(c_0_107,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_97,c_0_59])).

cnf(c_0_108,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_53,c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_55,c_0_88])).

cnf(c_0_110,negated_conjecture,
    ( ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_111,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k2_zfmisc_1(X2,X1),X2,X1)
    | k1_relat_1(k2_zfmisc_1(X2,X1)) != X2 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_101,c_0_51]),c_0_84])).

cnf(c_0_112,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_102,c_0_56])).

cnf(c_0_113,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_114,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X3)
    | ~ r1_tarski(X1,X3) ),
    inference(pm,[status(thm)],[c_0_103,c_0_59])).

cnf(c_0_115,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_104,c_0_105]),c_0_38])])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k10_relat_1(k2_zfmisc_1(esk2_0,esk3_0),X1),k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_106,c_0_93])).

cnf(c_0_117,negated_conjecture,
    ( esk4_0 = X1
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(pm,[status(thm)],[c_0_64,c_0_107])).

cnf(c_0_118,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_119,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk3_0,esk2_0)) != esk3_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_110,c_0_111]),c_0_112])).

cnf(c_0_120,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_relset_1(X1,X2,k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_84,c_0_113])).

cnf(c_0_121,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(pm,[status(thm)],[c_0_40,c_0_80])).

cnf(c_0_122,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),X1)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_114,c_0_115]),c_0_77])])).

cnf(c_0_123,negated_conjecture,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0)),k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_116,c_0_105]),c_0_96])])).

cnf(c_0_124,negated_conjecture,
    ( esk4_0 = X1
    | esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_117,c_0_65])).

cnf(c_0_125,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118,c_0_74]),c_0_37]),c_0_38])])).

cnf(c_0_126,negated_conjecture,
    ( k1_relset_1(esk3_0,esk2_0,k1_xboole_0) != esk3_0
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_119,c_0_120])).

cnf(c_0_127,negated_conjecture,
    ( k1_relset_1(X1,X2,k1_relat_1(esk4_0)) = k1_relat_1(k1_relat_1(esk4_0))
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_121,c_0_122])).

cnf(c_0_128,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = k1_relset_1(X1,X2,k1_xboole_0)
    | X2 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_84,c_0_54])).

cnf(c_0_129,negated_conjecture,
    ( k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0)) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_123]),c_0_77])])).

cnf(c_0_130,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_124,c_0_77])).

cnf(c_0_131,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125,c_0_91]),c_0_37]),c_0_38])])).

cnf(c_0_132,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk4_0
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_117,c_0_122])).

cnf(c_0_133,negated_conjecture,
    ( k1_relset_1(esk3_0,esk2_0,k1_xboole_0) != esk3_0
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_126,c_0_113]),c_0_77])])).

cnf(c_0_134,negated_conjecture,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_relat_1(k1_relat_1(esk4_0))
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_127,c_0_93])).

cnf(c_0_135,negated_conjecture,
    ( k1_relset_1(esk2_0,esk3_0,k1_xboole_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_136,negated_conjecture,
    ( X1 = k1_relat_1(esk4_0)
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,k1_relat_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_64,c_0_122])).

cnf(c_0_137,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(pm,[status(thm)],[c_0_50,c_0_59])).

cnf(c_0_138,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130,c_0_131])])).

cnf(c_0_139,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_87,c_0_132])).

cnf(c_0_140,negated_conjecture,
    ( k1_relat_1(k1_relat_1(esk4_0)) != esk3_0
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_133,c_0_134])).

cnf(c_0_141,negated_conjecture,
    ( k1_relat_1(k1_relat_1(esk4_0)) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_135,c_0_134])).

cnf(c_0_142,negated_conjecture,
    ( X1 = k1_relat_1(esk4_0)
    | esk3_0 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(pm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_143,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132,c_0_131])]),c_0_138]),c_0_138])).

cnf(c_0_144,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_relat_1(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_139,c_0_113])).

cnf(c_0_145,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk4_0))
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(pm,[status(thm)],[c_0_140,c_0_141])).

cnf(c_0_146,negated_conjecture,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142,c_0_131])]),c_0_138]),c_0_143])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144,c_0_131])]),c_0_138]),c_0_138]),c_0_138])).

cnf(c_0_148,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(pm,[status(thm)],[c_0_96,c_0_54])).

cnf(c_0_149,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_145,c_0_91]),c_0_37]),c_0_38])])).

cnf(c_0_150,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_146,c_0_147]),c_0_77])])).

cnf(c_0_151,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_138])).

cnf(c_0_152,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_148])).

cnf(c_0_153,negated_conjecture,
    ( ~ v1_xboole_0(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149,c_0_131])])).

cnf(c_0_154,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_150,c_0_74]),c_0_151]),c_0_152])])).

cnf(c_0_155,negated_conjecture,
    ( ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_153,c_0_138])).

cnf(c_0_156,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_154,c_0_91]),c_0_151]),c_0_152])])).

cnf(c_0_157,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_155,c_0_156]),c_0_77])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.04/1.22  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 1.04/1.22  # and selection function NoSelection.
% 1.04/1.22  #
% 1.04/1.22  # Preprocessing time       : 0.028 s
% 1.04/1.22  
% 1.04/1.22  # Proof found!
% 1.04/1.22  # SZS status Theorem
% 1.04/1.22  # SZS output start CNFRefutation
% 1.04/1.22  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 1.04/1.22  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 1.04/1.22  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 1.04/1.22  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.04/1.22  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.04/1.22  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.04/1.22  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.04/1.22  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.04/1.22  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 1.04/1.22  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 1.04/1.22  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.04/1.22  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.04/1.22  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.04/1.22  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.04/1.22  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 1.04/1.22  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 1.04/1.22  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.04/1.22  fof(t167_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.04/1.22  fof(t169_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 1.04/1.22  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 1.04/1.22  fof(c_0_20, plain, ![X39]:(((v1_funct_1(X39)|(~v1_relat_1(X39)|~v1_funct_1(X39)))&(v1_funct_2(X39,k1_relat_1(X39),k2_relat_1(X39))|(~v1_relat_1(X39)|~v1_funct_1(X39))))&(m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X39),k2_relat_1(X39))))|(~v1_relat_1(X39)|~v1_funct_1(X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 1.04/1.22  fof(c_0_21, plain, ![X26]:((k2_relat_1(X26)=k1_relat_1(k2_funct_1(X26))|~v2_funct_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(k1_relat_1(X26)=k2_relat_1(k2_funct_1(X26))|~v2_funct_1(X26)|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 1.04/1.22  fof(c_0_22, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_relset_1(X33,X34,X35)=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.04/1.22  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&((v2_funct_1(esk4_0)&k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0)&(~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 1.04/1.22  fof(c_0_24, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.04/1.22  cnf(c_0_25, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.04/1.22  cnf(c_0_26, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.04/1.22  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.04/1.22  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.04/1.22  cnf(c_0_29, negated_conjecture, (k2_relset_1(esk2_0,esk3_0,esk4_0)=esk3_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.04/1.22  cnf(c_0_30, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.04/1.22  fof(c_0_31, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|k1_relset_1(X30,X31,X32)=k1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.04/1.22  fof(c_0_32, plain, ![X15]:m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 1.04/1.22  fof(c_0_33, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 1.04/1.22  cnf(c_0_34, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 1.04/1.22  cnf(c_0_35, negated_conjecture, (k2_relat_1(esk4_0)=esk3_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 1.04/1.22  cnf(c_0_36, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.04/1.22  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.04/1.22  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_30, c_0_28])).
% 1.04/1.22  fof(c_0_39, plain, ![X36, X37, X38]:((((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&((~v1_funct_2(X38,X36,X37)|X38=k1_xboole_0|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X38!=k1_xboole_0|v1_funct_2(X38,X36,X37)|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.04/1.22  cnf(c_0_40, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 1.04/1.22  fof(c_0_41, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|~v1_xboole_0(X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 1.04/1.22  cnf(c_0_42, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 1.04/1.22  cnf(c_0_43, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.04/1.22  fof(c_0_44, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.04/1.22  cnf(c_0_45, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k2_relat_1(k2_funct_1(esk4_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_46, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.04/1.22  cnf(c_0_47, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.04/1.22  cnf(c_0_48, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,esk4_0)=k1_relat_1(esk4_0)), inference(pm,[status(thm)],[c_0_40, c_0_28])).
% 1.04/1.22  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.04/1.22  cnf(c_0_50, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.04/1.22  cnf(c_0_51, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 1.04/1.22  fof(c_0_52, plain, ![X4, X5, X6, X7, X8]:((~r1_tarski(X4,X5)|(~r2_hidden(X6,X4)|r2_hidden(X6,X5)))&((r2_hidden(esk1_2(X7,X8),X7)|r1_tarski(X7,X8))&(~r2_hidden(esk1_2(X7,X8),X8)|r1_tarski(X7,X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.04/1.22  cnf(c_0_53, negated_conjecture, (~v1_funct_1(k2_funct_1(esk4_0))|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.04/1.22  cnf(c_0_54, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.04/1.22  cnf(c_0_55, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,k1_relat_1(esk4_0))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45, c_0_46]), c_0_36]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_28]), c_0_48]), c_0_49])])).
% 1.04/1.22  fof(c_0_57, plain, ![X10, X11]:(((r1_tarski(X10,X11)|X10!=X11)&(r1_tarski(X11,X10)|X10!=X11))&(~r1_tarski(X10,X11)|~r1_tarski(X11,X10)|X10=X11)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.04/1.22  cnf(c_0_58, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(pm,[status(thm)],[c_0_50, c_0_51])).
% 1.04/1.22  cnf(c_0_59, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.04/1.22  fof(c_0_60, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.04/1.22  cnf(c_0_61, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_53, c_0_54])).
% 1.04/1.22  cnf(c_0_62, negated_conjecture, (v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_55, c_0_56])).
% 1.04/1.22  cnf(c_0_63, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.04/1.22  cnf(c_0_64, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 1.04/1.22  cnf(c_0_65, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_58, c_0_59])).
% 1.04/1.22  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.04/1.22  cnf(c_0_67, negated_conjecture, (esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_61, c_0_62])).
% 1.04/1.22  cnf(c_0_68, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k2_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_63, c_0_54])).
% 1.04/1.22  fof(c_0_69, plain, ![X25]:((v1_relat_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(v1_funct_1(k2_funct_1(X25))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 1.04/1.22  cnf(c_0_70, plain, (X1=X2|~v1_xboole_0(X1)|~r1_tarski(X2,X1)), inference(pm,[status(thm)],[c_0_64, c_0_65])).
% 1.04/1.22  cnf(c_0_71, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(pm,[status(thm)],[c_0_66, c_0_28])).
% 1.04/1.22  cnf(c_0_72, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_63, c_0_26])).
% 1.04/1.22  cnf(c_0_73, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_67, c_0_68])).
% 1.04/1.22  cnf(c_0_74, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.04/1.22  fof(c_0_75, plain, ![X24]:((k1_relat_1(X24)!=k1_xboole_0|k2_relat_1(X24)=k1_xboole_0|~v1_relat_1(X24))&(k2_relat_1(X24)!=k1_xboole_0|k1_relat_1(X24)=k1_xboole_0|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 1.04/1.22  cnf(c_0_76, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))), inference(pm,[status(thm)],[c_0_70, c_0_71])).
% 1.04/1.22  cnf(c_0_77, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.04/1.22  cnf(c_0_78, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_relat_1(k2_funct_1(esk4_0)))))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_35]), c_0_36]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_79, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.04/1.22  cnf(c_0_80, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 1.04/1.22  cnf(c_0_81, negated_conjecture, (k2_relat_1(k2_funct_1(esk4_0))!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_74]), c_0_37]), c_0_38])])).
% 1.04/1.22  fof(c_0_82, plain, ![X21, X22]:(~v1_relat_1(X22)|r1_tarski(k10_relat_1(X22,X21),k1_relat_1(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t167_relat_1])])).
% 1.04/1.22  cnf(c_0_83, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 1.04/1.22  cnf(c_0_84, plain, (k1_relset_1(X1,X2,k2_zfmisc_1(X1,X2))=k1_relat_1(k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_40, c_0_51])).
% 1.04/1.22  cnf(c_0_85, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_76, c_0_54]), c_0_77])])).
% 1.04/1.22  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_28, c_0_54])).
% 1.04/1.22  cnf(c_0_87, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_relat_1(esk4_0))))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_78, c_0_46]), c_0_36]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_88, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_79, c_0_28]), c_0_48]), c_0_49])])).
% 1.04/1.22  cnf(c_0_89, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~r1_tarski(k2_funct_1(esk4_0),k2_zfmisc_1(esk3_0,esk2_0))), inference(pm,[status(thm)],[c_0_53, c_0_80])).
% 1.04/1.22  cnf(c_0_90, negated_conjecture, (k1_relat_1(esk4_0)!=k1_xboole_0|esk2_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_46]), c_0_36]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_91, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 1.04/1.22  cnf(c_0_92, plain, (r1_tarski(k10_relat_1(X1,X2),k1_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 1.04/1.22  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_83, c_0_38]), c_0_35])).
% 1.04/1.22  fof(c_0_94, plain, ![X23]:(~v1_relat_1(X23)|k10_relat_1(X23,k2_relat_1(X23))=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t169_relat_1])])).
% 1.04/1.22  cnf(c_0_95, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0))=k1_relat_1(esk4_0)|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_84, c_0_85]), c_0_48])).
% 1.04/1.22  cnf(c_0_96, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_30, c_0_51])).
% 1.04/1.22  cnf(c_0_97, negated_conjecture, (esk3_0!=k1_xboole_0|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_86]), c_0_77])])).
% 1.04/1.22  cnf(c_0_98, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_87, c_0_88])).
% 1.04/1.22  cnf(c_0_99, negated_conjecture, (~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_89, c_0_65])).
% 1.04/1.22  cnf(c_0_100, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_70, c_0_65])).
% 1.04/1.22  cnf(c_0_101, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.04/1.22  cnf(c_0_102, negated_conjecture, (k1_relat_1(esk4_0)!=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_90, c_0_91]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_103, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X3)|~r1_tarski(X3,X1)), inference(pm,[status(thm)],[c_0_50, c_0_80])).
% 1.04/1.22  cnf(c_0_104, negated_conjecture, (r1_tarski(k10_relat_1(esk4_0,X1),k1_xboole_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_93]), c_0_38])])).
% 1.04/1.22  cnf(c_0_105, plain, (k10_relat_1(X1,k2_relat_1(X1))=k1_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 1.04/1.22  cnf(c_0_106, negated_conjecture, (r1_tarski(k10_relat_1(k2_zfmisc_1(esk2_0,esk3_0),X1),k1_relat_1(esk4_0))|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_92, c_0_95]), c_0_96])])).
% 1.04/1.22  cnf(c_0_107, negated_conjecture, (r1_tarski(esk4_0,X1)|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_97, c_0_59])).
% 1.04/1.22  cnf(c_0_108, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_53, c_0_98])).
% 1.04/1.22  cnf(c_0_109, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk4_0),esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_55, c_0_88])).
% 1.04/1.22  cnf(c_0_110, negated_conjecture, (~v1_funct_2(X1,esk3_0,esk2_0)|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_99, c_0_100])).
% 1.04/1.22  cnf(c_0_111, plain, (X1=k1_xboole_0|v1_funct_2(k2_zfmisc_1(X2,X1),X2,X1)|k1_relat_1(k2_zfmisc_1(X2,X1))!=X2), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_101, c_0_51]), c_0_84])).
% 1.04/1.22  cnf(c_0_112, negated_conjecture, (esk2_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_102, c_0_56])).
% 1.04/1.22  cnf(c_0_113, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.04/1.22  cnf(c_0_114, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X3)|~r1_tarski(X1,X3)), inference(pm,[status(thm)],[c_0_103, c_0_59])).
% 1.04/1.22  cnf(c_0_115, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k1_xboole_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_104, c_0_105]), c_0_38])])).
% 1.04/1.22  cnf(c_0_116, negated_conjecture, (r1_tarski(k10_relat_1(k2_zfmisc_1(esk2_0,esk3_0),X1),k1_xboole_0)|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_106, c_0_93])).
% 1.04/1.22  cnf(c_0_117, negated_conjecture, (esk4_0=X1|esk3_0!=k1_xboole_0|~r1_tarski(X1,esk4_0)), inference(pm,[status(thm)],[c_0_64, c_0_107])).
% 1.04/1.22  cnf(c_0_118, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_108, c_0_109])).
% 1.04/1.22  cnf(c_0_119, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk3_0,esk2_0))!=esk3_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_110, c_0_111]), c_0_112])).
% 1.04/1.22  cnf(c_0_120, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=k1_relset_1(X1,X2,k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_84, c_0_113])).
% 1.04/1.22  cnf(c_0_121, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(pm,[status(thm)],[c_0_40, c_0_80])).
% 1.04/1.22  cnf(c_0_122, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),X1)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_114, c_0_115]), c_0_77])])).
% 1.04/1.22  cnf(c_0_123, negated_conjecture, (r1_tarski(k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0)),k1_xboole_0)|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_116, c_0_105]), c_0_96])])).
% 1.04/1.22  cnf(c_0_124, negated_conjecture, (esk4_0=X1|esk3_0!=k1_xboole_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_117, c_0_65])).
% 1.04/1.22  cnf(c_0_125, negated_conjecture, (esk3_0=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118, c_0_74]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_126, negated_conjecture, (k1_relset_1(esk3_0,esk2_0,k1_xboole_0)!=esk3_0|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk2_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_119, c_0_120])).
% 1.04/1.22  cnf(c_0_127, negated_conjecture, (k1_relset_1(X1,X2,k1_relat_1(esk4_0))=k1_relat_1(k1_relat_1(esk4_0))|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_121, c_0_122])).
% 1.04/1.22  cnf(c_0_128, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=k1_relset_1(X1,X2,k1_xboole_0)|X2!=k1_xboole_0), inference(pm,[status(thm)],[c_0_84, c_0_54])).
% 1.04/1.22  cnf(c_0_129, negated_conjecture, (k1_relat_1(k2_zfmisc_1(esk2_0,esk3_0))=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_123]), c_0_77])])).
% 1.04/1.22  cnf(c_0_130, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_124, c_0_77])).
% 1.04/1.22  cnf(c_0_131, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_125, c_0_91]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_132, negated_conjecture, (k1_relat_1(esk4_0)=esk4_0|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_117, c_0_122])).
% 1.04/1.22  cnf(c_0_133, negated_conjecture, (k1_relset_1(esk3_0,esk2_0,k1_xboole_0)!=esk3_0|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_126, c_0_113]), c_0_77])])).
% 1.04/1.22  cnf(c_0_134, negated_conjecture, (k1_relset_1(X1,X2,k1_xboole_0)=k1_relat_1(k1_relat_1(esk4_0))|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_127, c_0_93])).
% 1.04/1.22  cnf(c_0_135, negated_conjecture, (k1_relset_1(esk2_0,esk3_0,k1_xboole_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_128, c_0_129])).
% 1.04/1.22  cnf(c_0_136, negated_conjecture, (X1=k1_relat_1(esk4_0)|esk3_0!=k1_xboole_0|~r1_tarski(X1,k1_relat_1(esk4_0))), inference(pm,[status(thm)],[c_0_64, c_0_122])).
% 1.04/1.22  cnf(c_0_137, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(pm,[status(thm)],[c_0_50, c_0_59])).
% 1.04/1.22  cnf(c_0_138, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_130, c_0_131])])).
% 1.04/1.22  cnf(c_0_139, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_87, c_0_132])).
% 1.04/1.22  cnf(c_0_140, negated_conjecture, (k1_relat_1(k1_relat_1(esk4_0))!=esk3_0|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_133, c_0_134])).
% 1.04/1.22  cnf(c_0_141, negated_conjecture, (k1_relat_1(k1_relat_1(esk4_0))=k1_xboole_0|esk3_0!=k1_xboole_0), inference(pm,[status(thm)],[c_0_135, c_0_134])).
% 1.04/1.22  cnf(c_0_142, negated_conjecture, (X1=k1_relat_1(esk4_0)|esk3_0!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(pm,[status(thm)],[c_0_136, c_0_137])).
% 1.04/1.22  cnf(c_0_143, negated_conjecture, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_132, c_0_131])]), c_0_138]), c_0_138])).
% 1.04/1.22  cnf(c_0_144, negated_conjecture, (m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_relat_1(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_139, c_0_113])).
% 1.04/1.22  cnf(c_0_145, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk4_0))|~v1_xboole_0(k2_funct_1(esk4_0))), inference(pm,[status(thm)],[c_0_140, c_0_141])).
% 1.04/1.22  cnf(c_0_146, negated_conjecture, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_142, c_0_131])]), c_0_138]), c_0_143])).
% 1.04/1.22  cnf(c_0_147, negated_conjecture, (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))|~v1_funct_1(k2_funct_1(k1_xboole_0))|~v1_relat_1(k2_funct_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_144, c_0_131])]), c_0_138]), c_0_138]), c_0_138])).
% 1.04/1.22  cnf(c_0_148, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(pm,[status(thm)],[c_0_96, c_0_54])).
% 1.04/1.22  cnf(c_0_149, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_xboole_0(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_145, c_0_91]), c_0_37]), c_0_38])])).
% 1.04/1.22  cnf(c_0_150, negated_conjecture, (k2_funct_1(k1_xboole_0)=k1_xboole_0|~v1_funct_1(k2_funct_1(k1_xboole_0))|~v1_relat_1(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_146, c_0_147]), c_0_77])])).
% 1.04/1.22  cnf(c_0_151, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_37, c_0_138])).
% 1.04/1.22  cnf(c_0_152, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_148])).
% 1.04/1.22  cnf(c_0_153, negated_conjecture, (~v1_xboole_0(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_149, c_0_131])])).
% 1.04/1.22  cnf(c_0_154, negated_conjecture, (k2_funct_1(k1_xboole_0)=k1_xboole_0|~v1_funct_1(k2_funct_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_150, c_0_74]), c_0_151]), c_0_152])])).
% 1.04/1.22  cnf(c_0_155, negated_conjecture, (~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_153, c_0_138])).
% 1.04/1.22  cnf(c_0_156, negated_conjecture, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_154, c_0_91]), c_0_151]), c_0_152])])).
% 1.04/1.22  cnf(c_0_157, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_155, c_0_156]), c_0_77])]), ['proof']).
% 1.04/1.22  # SZS output end CNFRefutation
% 1.04/1.22  # Proof object total steps             : 158
% 1.04/1.22  # Proof object clause steps            : 120
% 1.04/1.22  # Proof object formula steps           : 38
% 1.04/1.22  # Proof object conjectures             : 79
% 1.04/1.22  # Proof object clause conjectures      : 76
% 1.04/1.22  # Proof object formula conjectures     : 3
% 1.04/1.22  # Proof object initial clauses used    : 31
% 1.04/1.22  # Proof object initial formulas used   : 19
% 1.04/1.22  # Proof object generating inferences   : 80
% 1.04/1.22  # Proof object simplifying inferences  : 95
% 1.04/1.22  # Training examples: 0 positive, 0 negative
% 1.04/1.22  # Parsed axioms                        : 19
% 1.04/1.22  # Removed by relevancy pruning/SinE    : 0
% 1.04/1.22  # Initial clauses                      : 41
% 1.04/1.22  # Removed in clause preprocessing      : 2
% 1.04/1.22  # Initial clauses in saturation        : 39
% 1.04/1.22  # Processed clauses                    : 11223
% 1.04/1.22  # ...of these trivial                  : 118
% 1.04/1.22  # ...subsumed                          : 9698
% 1.04/1.22  # ...remaining for further processing  : 1407
% 1.04/1.22  # Other redundant clauses eliminated   : 0
% 1.04/1.22  # Clauses deleted for lack of memory   : 0
% 1.04/1.22  # Backward-subsumed                    : 184
% 1.04/1.22  # Backward-rewritten                   : 1005
% 1.04/1.22  # Generated clauses                    : 69519
% 1.04/1.22  # ...of the previous two non-trivial   : 65528
% 1.04/1.22  # Contextual simplify-reflections      : 0
% 1.04/1.22  # Paramodulations                      : 69507
% 1.04/1.22  # Factorizations                       : 0
% 1.04/1.22  # Equation resolutions                 : 12
% 1.04/1.22  # Propositional unsat checks           : 0
% 1.04/1.22  #    Propositional check models        : 0
% 1.04/1.22  #    Propositional check unsatisfiable : 0
% 1.04/1.22  #    Propositional clauses             : 0
% 1.04/1.22  #    Propositional clauses after purity: 0
% 1.04/1.22  #    Propositional unsat core size     : 0
% 1.04/1.22  #    Propositional preprocessing time  : 0.000
% 1.04/1.22  #    Propositional encoding time       : 0.000
% 1.04/1.22  #    Propositional solver time         : 0.000
% 1.04/1.22  #    Success case prop preproc time    : 0.000
% 1.04/1.22  #    Success case prop encoding time   : 0.000
% 1.04/1.22  #    Success case prop solver time     : 0.000
% 1.04/1.22  # Current number of processed clauses  : 218
% 1.04/1.22  #    Positive orientable unit clauses  : 22
% 1.04/1.22  #    Positive unorientable unit clauses: 0
% 1.04/1.22  #    Negative unit clauses             : 2
% 1.04/1.22  #    Non-unit-clauses                  : 194
% 1.04/1.22  # Current number of unprocessed clauses: 53937
% 1.04/1.22  # ...number of literals in the above   : 267819
% 1.04/1.22  # Current number of archived formulas  : 0
% 1.04/1.22  # Current number of archived clauses   : 1190
% 1.04/1.22  # Clause-clause subsumption calls (NU) : 261979
% 1.04/1.22  # Rec. Clause-clause subsumption calls : 188740
% 1.04/1.22  # Non-unit clause-clause subsumptions  : 8645
% 1.04/1.22  # Unit Clause-clause subsumption calls : 684
% 1.04/1.22  # Rewrite failures with RHS unbound    : 0
% 1.04/1.22  # BW rewrite match attempts            : 41
% 1.04/1.22  # BW rewrite match successes           : 23
% 1.04/1.22  # Condensation attempts                : 0
% 1.04/1.22  # Condensation successes               : 0
% 1.04/1.22  # Termbank termtop insertions          : 476305
% 1.08/1.22  
% 1.08/1.22  # -------------------------------------------------
% 1.08/1.22  # User time                : 0.846 s
% 1.08/1.22  # System time              : 0.032 s
% 1.08/1.22  # Total time               : 0.878 s
% 1.08/1.22  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
