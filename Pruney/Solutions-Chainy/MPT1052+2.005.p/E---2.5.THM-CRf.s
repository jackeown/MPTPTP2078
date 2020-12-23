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
% DateTime   : Thu Dec  3 11:07:14 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 (1438 expanded)
%              Number of clauses        :   49 ( 666 expanded)
%              Number of leaves         :   13 ( 356 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 (3864 expanded)
%              Number of equality atoms :   52 (1006 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

fof(t121_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X3,k1_funct_2(X1,X2))
     => ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(t160_funct_2,axiom,(
    ! [X1,X2] : k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc3_funct_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => v1_xboole_0(k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

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

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( r2_hidden(X3,k1_funct_2(X1,X2))
         => ( k1_relat_1(X3) = X1
            & r1_tarski(k2_relat_1(X3),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t169_funct_2])).

fof(c_0_14,plain,(
    ! [X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | ~ r2_hidden(X33,k1_funct_2(X31,X32)) )
      & ( v1_funct_2(X33,X31,X32)
        | ~ r2_hidden(X33,k1_funct_2(X31,X32)) )
      & ( m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ r2_hidden(X33,k1_funct_2(X31,X32)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).

fof(c_0_15,plain,(
    ! [X34,X35] : k5_partfun1(X34,X35,k3_partfun1(k1_xboole_0,X34,X35)) = k1_funct_2(X34,X35) ),
    inference(variable_rename,[status(thm)],[t160_funct_2])).

fof(c_0_16,negated_conjecture,
    ( v1_relat_1(esk5_0)
    & v1_funct_1(esk5_0)
    & r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))
    & ( k1_relat_1(esk5_0) != esk3_0
      | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)) = k1_funct_2(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_21,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ( ~ r1_tarski(X10,X11)
        | ~ r2_hidden(X12,X10)
        | r2_hidden(X12,X11) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | r1_tarski(X13,X14) )
      & ( ~ r2_hidden(esk2_2(X13,X14),X14)
        | r1_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

fof(c_0_25,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_26,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X18,X19] :
      ( ( ~ v5_relat_1(X19,X18)
        | r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(k2_relat_1(X19),X18)
        | v5_relat_1(X19,X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_31,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X16,X17] :
      ( ~ r1_tarski(X16,X17)
      | k2_xboole_0(X16,X17) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_35,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | ~ v1_xboole_0(X30)
      | v1_xboole_0(k1_funct_2(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).

cnf(c_0_36,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k1_funct_2(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(esk5_0) != esk3_0
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_relset_1(esk3_0,esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v5_relat_1(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_42,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X5,X4) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k1_funct_2(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_46,plain,(
    ! [X26,X27,X28] :
      ( ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X27 = k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X26 = k1_relset_1(X26,X27,X28)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X26 != k1_relset_1(X26,X27,X28)
        | v1_funct_2(X28,X26,X27)
        | X26 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( ~ v1_funct_2(X28,X26,X27)
        | X28 = k1_xboole_0
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( X28 != k1_xboole_0
        | v1_funct_2(X28,X26,X27)
        | X26 = k1_xboole_0
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_47,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) != esk3_0
    | ~ r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])])).

cnf(c_0_50,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_51,plain,
    ( k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_18])).

cnf(c_0_53,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_24])).

cnf(c_0_55,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk5_0) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_56,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,plain,
    ( v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_29]),c_0_54])]),c_0_55])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_56])).

cnf(c_0_61,plain,
    ( r1_tarski(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)),X2)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk3_0,k1_xboole_0,k3_partfun1(k1_xboole_0,esk3_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59])).

cnf(c_0_63,plain,
    ( k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_34])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_64])).

cnf(c_0_66,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_59])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(esk3_0,k1_xboole_0,esk5_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_55,c_0_59])).

cnf(c_0_70,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_59]),c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_68]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])]),c_0_73]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:35:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.37  # and selection function PSelectComplexPreferEQ.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.028 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t169_funct_2, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 0.20/0.37  fof(t121_funct_2, axiom, ![X1, X2, X3]:(r2_hidden(X3,k1_funct_2(X1,X2))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 0.20/0.37  fof(t160_funct_2, axiom, ![X1, X2]:k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_funct_2)).
% 0.20/0.37  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.37  fof(fc3_funct_2, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>v1_xboole_0(k1_funct_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 0.20/0.37  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.37  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X3,k1_funct_2(X1,X2))=>(k1_relat_1(X3)=X1&r1_tarski(k2_relat_1(X3),X2))))), inference(assume_negation,[status(cth)],[t169_funct_2])).
% 0.20/0.37  fof(c_0_14, plain, ![X31, X32, X33]:(((v1_funct_1(X33)|~r2_hidden(X33,k1_funct_2(X31,X32)))&(v1_funct_2(X33,X31,X32)|~r2_hidden(X33,k1_funct_2(X31,X32))))&(m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|~r2_hidden(X33,k1_funct_2(X31,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_2])])])).
% 0.20/0.37  fof(c_0_15, plain, ![X34, X35]:k5_partfun1(X34,X35,k3_partfun1(k1_xboole_0,X34,X35))=k1_funct_2(X34,X35), inference(variable_rename,[status(thm)],[t160_funct_2])).
% 0.20/0.37  fof(c_0_16, negated_conjecture, ((v1_relat_1(esk5_0)&v1_funct_1(esk5_0))&(r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))&(k1_relat_1(esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.20/0.37  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_18, plain, (k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))=k1_funct_2(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_19, negated_conjecture, (r2_hidden(esk5_0,k1_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  fof(c_0_20, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_21, plain, ![X10, X11, X12, X13, X14]:((~r1_tarski(X10,X11)|(~r2_hidden(X12,X10)|r2_hidden(X12,X11)))&((r2_hidden(esk2_2(X13,X14),X13)|r1_tarski(X13,X14))&(~r2_hidden(esk2_2(X13,X14),X14)|r1_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.37  fof(c_0_22, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k1_relset_1(X23,X24,X25)=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.37  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_0,k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0)))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.20/0.37  fof(c_0_25, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.37  cnf(c_0_26, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_27, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.37  fof(c_0_30, plain, ![X18, X19]:((~v5_relat_1(X19,X18)|r1_tarski(k2_relat_1(X19),X18)|~v1_relat_1(X19))&(~r1_tarski(k2_relat_1(X19),X18)|v5_relat_1(X19,X18)|~v1_relat_1(X19))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.37  cnf(c_0_31, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  fof(c_0_32, plain, ![X16, X17]:(~r1_tarski(X16,X17)|k2_xboole_0(X16,X17)=X17), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.37  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_34, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.37  fof(c_0_35, plain, ![X29, X30]:(v1_xboole_0(X29)|~v1_xboole_0(X30)|v1_xboole_0(k1_funct_2(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_funct_2])])])).
% 0.20/0.37  cnf(c_0_36, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k1_funct_2(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (k1_relat_1(esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk5_0)=k1_relset_1(esk3_0,esk4_0,esk5_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.37  cnf(c_0_39, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (v5_relat_1(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_31, c_0_29])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  fof(c_0_42, plain, ![X4, X5]:k2_xboole_0(X4,X5)=k2_xboole_0(X5,X4), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.37  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.37  cnf(c_0_44, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.37  cnf(c_0_45, plain, (v1_xboole_0(X1)|v1_xboole_0(k1_funct_2(X1,X2))|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.37  fof(c_0_46, plain, ![X26, X27, X28]:((((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X27=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&((~v1_funct_2(X28,X26,X27)|X26=k1_relset_1(X26,X27,X28)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X26!=k1_relset_1(X26,X27,X28)|v1_funct_2(X28,X26,X27)|X26!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&((~v1_funct_2(X28,X26,X27)|X28=k1_xboole_0|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(X28!=k1_xboole_0|v1_funct_2(X28,X26,X27)|X26=k1_xboole_0|X27!=k1_xboole_0|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.37  cnf(c_0_47, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,k3_partfun1(k1_xboole_0,X2,X3)))), inference(rw,[status(thm)],[c_0_36, c_0_18])).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)!=esk3_0|~r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(rw,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, (r1_tarski(k2_relat_1(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])])).
% 0.20/0.37  cnf(c_0_50, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.37  cnf(c_0_51, plain, (k2_xboole_0(k1_xboole_0,X1)=X1), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.37  cnf(c_0_52, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))|~v1_xboole_0(X2)), inference(rw,[status(thm)],[c_0_45, c_0_18])).
% 0.20/0.37  cnf(c_0_53, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_24])).
% 0.20/0.37  cnf(c_0_55, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk5_0)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 0.20/0.37  cnf(c_0_56, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.37  cnf(c_0_57, plain, (v1_xboole_0(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)))|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_34])).
% 0.20/0.37  cnf(c_0_58, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk3_0,esk4_0,k3_partfun1(k1_xboole_0,esk3_0,esk4_0)))), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.20/0.37  cnf(c_0_59, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_29]), c_0_54])]), c_0_55])).
% 0.20/0.37  cnf(c_0_60, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_56])).
% 0.20/0.37  cnf(c_0_61, plain, (r1_tarski(k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0)),X2)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_57])).
% 0.20/0.37  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk3_0,k1_xboole_0,k3_partfun1(k1_xboole_0,esk3_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59])).
% 0.20/0.37  cnf(c_0_63, plain, (k5_partfun1(X1,k1_xboole_0,k3_partfun1(k1_xboole_0,X1,k1_xboole_0))=k1_xboole_0|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.37  cnf(c_0_64, negated_conjecture, (v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_34])])).
% 0.20/0.37  cnf(c_0_65, negated_conjecture, (r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_33, c_0_64])).
% 0.20/0.37  cnf(c_0_66, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.37  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_29, c_0_59])).
% 0.20/0.37  cnf(c_0_68, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_60, c_0_65])).
% 0.20/0.37  cnf(c_0_69, negated_conjecture, (k1_relset_1(esk3_0,k1_xboole_0,esk5_0)!=esk3_0), inference(rw,[status(thm)],[c_0_55, c_0_59])).
% 0.20/0.37  cnf(c_0_70, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_66])).
% 0.20/0.37  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.37  cnf(c_0_72, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_59]), c_0_68])).
% 0.20/0.37  cnf(c_0_73, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk5_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_68]), c_0_68])).
% 0.20/0.37  cnf(c_0_74, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])]), c_0_73]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 75
% 0.20/0.37  # Proof object clause steps            : 49
% 0.20/0.37  # Proof object formula steps           : 26
% 0.20/0.37  # Proof object conjectures             : 26
% 0.20/0.37  # Proof object clause conjectures      : 23
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 17
% 0.20/0.37  # Proof object initial formulas used   : 13
% 0.20/0.37  # Proof object generating inferences   : 19
% 0.20/0.37  # Proof object simplifying inferences  : 27
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 13
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 28
% 0.20/0.37  # Removed in clause preprocessing      : 1
% 0.20/0.37  # Initial clauses in saturation        : 27
% 0.20/0.37  # Processed clauses                    : 116
% 0.20/0.37  # ...of these trivial                  : 7
% 0.20/0.37  # ...subsumed                          : 3
% 0.20/0.37  # ...remaining for further processing  : 106
% 0.20/0.37  # Other redundant clauses eliminated   : 7
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 21
% 0.20/0.37  # Generated clauses                    : 120
% 0.20/0.37  # ...of the previous two non-trivial   : 96
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 106
% 0.20/0.37  # Factorizations                       : 8
% 0.20/0.37  # Equation resolutions                 : 7
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 54
% 0.20/0.37  #    Positive orientable unit clauses  : 17
% 0.20/0.37  #    Positive unorientable unit clauses: 1
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 34
% 0.20/0.37  # Current number of unprocessed clauses: 32
% 0.20/0.37  # ...number of literals in the above   : 68
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 49
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 166
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 90
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.37  # Unit Clause-clause subsumption calls : 20
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 14
% 0.20/0.37  # BW rewrite match successes           : 7
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3218
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.032 s
% 0.20/0.38  # System time              : 0.005 s
% 0.20/0.38  # Total time               : 0.037 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
