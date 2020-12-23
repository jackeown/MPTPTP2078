%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 (8282 expanded)
%              Number of clauses        :   64 (3623 expanded)
%              Number of leaves         :   21 (2072 expanded)
%              Depth                    :   16
%              Number of atoms          :  276 (24154 expanded)
%              Number of equality atoms :  103 (7972 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t169_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X3,k1_funct_2(X1,X2))
       => ( k1_relat_1(X3) = X1
          & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(t160_funct_2,axiom,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_funct_2)).

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

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t194_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(cc1_relat_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

fof(c_0_22,plain,(
    ! [X41,X42,X43] :
      ( ( v1_funct_1(X43)
        | ~ r2_hidden(X43,k1_funct_2(X41,X42)) )
      & ( v1_funct_2(X43,X41,X42)
        | ~ r2_hidden(X43,k1_funct_2(X41,X42)) )
      & ( m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ r2_hidden(X43,k1_funct_2(X41,X42)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

fof(c_0_23,plain,(
    ! [X44,X45] : k5_partfun1(X44,X45,k3_partfun1(k1_xboole_0,X44,X45)) = k1_funct_2(X44,X45) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_24,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))
    & ( k1_relat_1(esk5_0) != esk3_0
      | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
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

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_32,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_28,c_0_26])).

fof(c_0_33,plain,(
    ! [X29] :
      ( ( k1_relat_1(X29) != k1_xboole_0
        | k2_relat_1(X29) = k1_xboole_0
        | ~ v1_relat_1(X29) )
      & ( k2_relat_1(X29) != k1_xboole_0
        | k1_relat_1(X29) = k1_xboole_0
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

fof(c_0_34,plain,(
    ! [X11] : r1_tarski(k1_xboole_0,X11) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_35,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k1_relset_1(X33,X34,X35) = k1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_36,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_31])).

fof(c_0_39,plain,(
    ! [X26,X27] :
      ( ( r1_tarski(k1_relat_1(X26),k1_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) )
      & ( r1_tarski(k2_relat_1(X26),k2_relat_1(X27))
        | ~ r1_tarski(X26,X27)
        | ~ v1_relat_1(X27)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_40,plain,(
    ! [X24,X25] :
      ( ( k1_relat_1(k2_zfmisc_1(X24,X25)) = X24
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X24,X25)) = X25
        | X24 = k1_xboole_0
        | X25 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

fof(c_0_41,plain,(
    ! [X20,X21] : v1_relat_1(k2_zfmisc_1(X20,X21)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_42,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_47,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) = esk3_0
    | k1_xboole_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])])).

fof(c_0_49,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,k1_xboole_0)
      | X12 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_50,plain,(
    ! [X22,X23] : r1_tarski(k2_relat_1(k2_zfmisc_1(X22,X23)),X23) ),
    inference(variable_rename,[status(thm)],[t194_relat_1])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,X2)) = X2
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_53,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0
    | k1_relat_1(esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0
    | k1_xboole_0 = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_37])])).

fof(c_0_57,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | v1_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).

fof(c_0_58,plain,(
    ! [X28] :
      ( ( k1_relat_1(X28) != k1_xboole_0
        | X28 = k1_xboole_0
        | ~ v1_relat_1(X28) )
      & ( k2_relat_1(X28) != k1_xboole_0
        | X28 = k1_xboole_0
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k2_relat_1(X3),X2)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | k1_xboole_0 != esk3_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_64,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_66,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( k1_xboole_0 = esk4_0
    | r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_46])]),c_0_63])).

cnf(c_0_70,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_71,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_72,plain,(
    ! [X39,X40] :
      ( v1_xboole_0(X39)
      | ~ v1_xboole_0(X40)
      | v1_xboole_0(k1_funct_2(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

cnf(c_0_73,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_53])])).

cnf(c_0_75,negated_conjecture,
    ( k1_xboole_0 = esk4_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_69]),c_0_56])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_70]),c_0_71])])).

fof(c_0_77,plain,(
    ! [X4,X5,X6] :
      ( ( ~ v1_xboole_0(X4)
        | ~ r2_hidden(X5,X4) )
      & ( r2_hidden(esk1_1(X6),X6)
        | v1_xboole_0(X6) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_62])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(X1,esk4_0) = esk4_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75])).

cnf(c_0_81,plain,
    ( r1_tarski(esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_45,c_0_75])).

cnf(c_0_82,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_83,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_76]),c_0_45])])).

fof(c_0_84,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | X8 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_85,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_78,c_0_26])).

cnf(c_0_87,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_80]),c_0_80]),c_0_81])])).

cnf(c_0_88,plain,
    ( v1_xboole_0(esk4_0) ),
    inference(rw,[status(thm)],[c_0_65,c_0_75])).

cnf(c_0_89,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_31])).

cnf(c_0_92,plain,
    ( v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(esk5_0,X1,X2)))
    | v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_75]),c_0_87])).

cnf(c_0_93,plain,
    ( v1_xboole_0(esk5_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( k1_xboole_0 != esk3_0
    | ~ r1_tarski(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_89]),c_0_46])])).

cnf(c_0_95,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_96,plain,
    ( X1 = esk4_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_90,c_0_75])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk3_0,esk5_0,k3_partfun1(esk5_0,esk3_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_75]),c_0_87]),c_0_87]),c_0_87])).

cnf(c_0_98,plain,
    ( v1_xboole_0(k5_partfun1(X1,esk5_0,k3_partfun1(esk5_0,X1,esk5_0)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,negated_conjecture,
    ( esk4_0 != esk3_0
    | ~ r1_tarski(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_75]),c_0_75])).

cnf(c_0_100,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_95])).

cnf(c_0_101,plain,
    ( X1 = esk5_0
    | ~ v1_xboole_0(X1) ),
    inference(rw,[status(thm)],[c_0_96,c_0_87])).

cnf(c_0_102,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( esk3_0 != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_87]),c_0_87]),c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:29:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07____S_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.41  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_funct_2)).
% 0.20/0.41  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.41  fof(t160_funct_2, axiom, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_funct_2)).
% 0.20/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.41  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.20/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.41  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.20/0.41  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.20/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.20/0.41  fof(t194_relat_1, axiom, ![X1, X2]:r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 0.20/0.41  fof(cc1_relat_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 0.20/0.41  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.41  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.20/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.41  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.41  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.20/0.41  fof(c_0_22, plain, ![X41, X42, X43]:(((v1_funct_1(X43)|~r2_hidden(X43,k1_funct_2(X41,X42)))&(v1_funct_2(X43,X41,X42)|~r2_hidden(X43,k1_funct_2(X41,X42))))&(m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~r2_hidden(X43,k1_funct_2(X41,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.20/0.41  fof(c_0_23, plain, ![X44, X45]:k5_partfun1(X44,X45,k3_partfun1(k1_xboole_0,X44,X45))=k1_funct_2(X44,X45), inference(variable_rename,[status(thm)],[t160_funct_2])).
% 0.20/0.41  fof(c_0_24, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))&(k1_relat_1(esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.20/0.41  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  cnf(c_0_26, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_28, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.41  fof(c_0_29, plain, ![X36, X37, X38]:((((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X37=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&((~v1_funct_2(X38,X36,X37)|X36=k1_relset_1(X36,X37,X38)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X36!=k1_relset_1(X36,X37,X38)|v1_funct_2(X38,X36,X37)|X36!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&((~v1_funct_2(X38,X36,X37)|X38=k1_xboole_0|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(X38!=k1_xboole_0|v1_funct_2(X38,X36,X37)|X36=k1_xboole_0|X37!=k1_xboole_0|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.41  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.41  cnf(c_0_31, negated_conjecture, (r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.41  cnf(c_0_32, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_28, c_0_26])).
% 0.20/0.41  fof(c_0_33, plain, ![X29]:((k1_relat_1(X29)!=k1_xboole_0|k2_relat_1(X29)=k1_xboole_0|~v1_relat_1(X29))&(k2_relat_1(X29)!=k1_xboole_0|k1_relat_1(X29)=k1_xboole_0|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.20/0.41  fof(c_0_34, plain, ![X11]:r1_tarski(k1_xboole_0,X11), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.41  fof(c_0_35, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k1_relset_1(X33,X34,X35)=k1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.41  cnf(c_0_36, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.41  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_31])).
% 0.20/0.41  fof(c_0_39, plain, ![X26, X27]:((r1_tarski(k1_relat_1(X26),k1_relat_1(X27))|~r1_tarski(X26,X27)|~v1_relat_1(X27)|~v1_relat_1(X26))&(r1_tarski(k2_relat_1(X26),k2_relat_1(X27))|~r1_tarski(X26,X27)|~v1_relat_1(X27)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.20/0.41  fof(c_0_40, plain, ![X24, X25]:((k1_relat_1(k2_zfmisc_1(X24,X25))=X24|(X24=k1_xboole_0|X25=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X24,X25))=X25|(X24=k1_xboole_0|X25=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.20/0.41  fof(c_0_41, plain, ![X20, X21]:v1_relat_1(k2_zfmisc_1(X20,X21)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.41  fof(c_0_42, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_44, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_45, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.41  cnf(c_0_47, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)=esk3_0|k1_xboole_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])])).
% 0.20/0.41  fof(c_0_49, plain, ![X12]:(~r1_tarski(X12,k1_xboole_0)|X12=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.20/0.41  fof(c_0_50, plain, ![X22, X23]:r1_tarski(k2_relat_1(k2_zfmisc_1(X22,X23)),X23), inference(variable_rename,[status(thm)],[t194_relat_1])).
% 0.20/0.41  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_52, plain, (k2_relat_1(k2_zfmisc_1(X1,X2))=X2|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.41  cnf(c_0_53, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.41  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0|k1_relat_1(esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0|k1_xboole_0=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_37])])).
% 0.20/0.41  fof(c_0_57, plain, ![X19]:(~v1_xboole_0(X19)|v1_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relat_1])])).
% 0.20/0.41  fof(c_0_58, plain, ![X28]:((k1_relat_1(X28)!=k1_xboole_0|X28=k1_xboole_0|~v1_relat_1(X28))&(k2_relat_1(X28)!=k1_xboole_0|X28=k1_xboole_0|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.41  cnf(c_0_59, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.41  cnf(c_0_60, plain, (r1_tarski(k2_relat_1(k2_zfmisc_1(X1,X2)),X2)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.41  cnf(c_0_61, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k2_relat_1(X3),X2)|~v1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_54, c_0_37])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k1_xboole_0=esk4_0|k1_xboole_0!=esk3_0), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.41  cnf(c_0_64, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_65, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.41  fof(c_0_66, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  cnf(c_0_67, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_68, plain, (k2_relat_1(k2_zfmisc_1(X1,k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k1_xboole_0=esk4_0|r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_46])]), c_0_63])).
% 0.20/0.41  cnf(c_0_70, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.41  cnf(c_0_71, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.41  fof(c_0_72, plain, ![X39, X40]:(v1_xboole_0(X39)|~v1_xboole_0(X40)|v1_xboole_0(k1_funct_2(X39,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.20/0.41  cnf(c_0_73, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_74, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_53])])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (k1_xboole_0=esk4_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_69]), c_0_56])).
% 0.20/0.41  cnf(c_0_76, plain, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_70]), c_0_71])])).
% 0.20/0.41  fof(c_0_77, plain, ![X4, X5, X6]:((~v1_xboole_0(X4)|~r2_hidden(X5,X4))&(r2_hidden(esk1_1(X6),X6)|v1_xboole_0(X6))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.41  cnf(c_0_78, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=esk5_0|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_73, c_0_62])).
% 0.20/0.41  cnf(c_0_80, plain, (k2_zfmisc_1(X1,esk4_0)=esk4_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75])).
% 0.20/0.41  cnf(c_0_81, plain, (r1_tarski(esk4_0,X1)), inference(rw,[status(thm)],[c_0_45, c_0_75])).
% 0.20/0.41  cnf(c_0_82, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_83, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_76]), c_0_45])])).
% 0.20/0.41  fof(c_0_84, plain, ![X8]:(~v1_xboole_0(X8)|X8=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.41  cnf(c_0_85, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.20/0.41  cnf(c_0_86, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_78, c_0_26])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (esk4_0=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_80]), c_0_80]), c_0_81])])).
% 0.20/0.41  cnf(c_0_88, plain, (v1_xboole_0(esk4_0)), inference(rw,[status(thm)],[c_0_65, c_0_75])).
% 0.20/0.41  cnf(c_0_89, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.41  cnf(c_0_90, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_85, c_0_31])).
% 0.20/0.41  cnf(c_0_92, plain, (v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(esk5_0,X1,X2)))|v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_75]), c_0_87])).
% 0.20/0.41  cnf(c_0_93, plain, (v1_xboole_0(esk5_0)), inference(rw,[status(thm)],[c_0_88, c_0_87])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (k1_xboole_0!=esk3_0|~r1_tarski(esk5_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_89]), c_0_46])])).
% 0.20/0.41  cnf(c_0_95, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.20/0.41  cnf(c_0_96, plain, (X1=esk4_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_90, c_0_75])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk3_0,esk5_0,k3_partfun1(esk5_0,esk3_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_75]), c_0_87]), c_0_87]), c_0_87])).
% 0.20/0.41  cnf(c_0_98, plain, (v1_xboole_0(k5_partfun1(X1,esk5_0,k3_partfun1(esk5_0,X1,esk5_0)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.20/0.41  cnf(c_0_99, negated_conjecture, (esk4_0!=esk3_0|~r1_tarski(esk5_0,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_75]), c_0_75])).
% 0.20/0.41  cnf(c_0_100, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_95])).
% 0.20/0.41  cnf(c_0_101, plain, (X1=esk5_0|~v1_xboole_0(X1)), inference(rw,[status(thm)],[c_0_96, c_0_87])).
% 0.20/0.41  cnf(c_0_102, negated_conjecture, (v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.20/0.41  cnf(c_0_103, negated_conjecture, (esk3_0!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_87]), c_0_87]), c_0_100])])).
% 0.20/0.41  cnf(c_0_104, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 105
% 0.20/0.41  # Proof object clause steps            : 64
% 0.20/0.41  # Proof object formula steps           : 41
% 0.20/0.41  # Proof object conjectures             : 25
% 0.20/0.41  # Proof object clause conjectures      : 22
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 26
% 0.20/0.41  # Proof object initial formulas used   : 21
% 0.20/0.41  # Proof object generating inferences   : 22
% 0.20/0.41  # Proof object simplifying inferences  : 50
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 25
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 47
% 0.20/0.41  # Removed in clause preprocessing      : 1
% 0.20/0.41  # Initial clauses in saturation        : 46
% 0.20/0.41  # Processed clauses                    : 431
% 0.20/0.41  # ...of these trivial                  : 9
% 0.20/0.41  # ...subsumed                          : 140
% 0.20/0.41  # ...remaining for further processing  : 282
% 0.20/0.41  # Other redundant clauses eliminated   : 10
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 1
% 0.20/0.41  # Backward-rewritten                   : 95
% 0.20/0.41  # Generated clauses                    : 867
% 0.20/0.41  # ...of the previous two non-trivial   : 614
% 0.20/0.41  # Contextual simplify-reflections      : 4
% 0.20/0.41  # Paramodulations                      : 858
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 10
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 135
% 0.20/0.41  #    Positive orientable unit clauses  : 25
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 3
% 0.20/0.41  #    Non-unit-clauses                  : 107
% 0.20/0.41  # Current number of unprocessed clauses: 225
% 0.20/0.41  # ...number of literals in the above   : 1209
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 142
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 3833
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 2279
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 138
% 0.20/0.41  # Unit Clause-clause subsumption calls : 22
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 17
% 0.20/0.41  # BW rewrite match successes           : 6
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 16681
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.051 s
% 0.20/0.41  # System time              : 0.008 s
% 0.20/0.41  # Total time               : 0.060 s
% 0.20/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
