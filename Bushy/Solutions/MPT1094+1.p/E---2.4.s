%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : finset_1__t29_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  93 expanded)
%              Number of clauses        :   23 (  36 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  117 ( 281 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t3_subset)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t21_relat_1)).

fof(t100_funct_3,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t100_funct_3)).

fof(redefinition_k9_funct_3,axiom,(
    ! [X1,X2] : k9_funct_3(X1,X2) = k7_funct_3(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',redefinition_k9_funct_3)).

fof(cc2_finset_1,axiom,(
    ! [X1] :
      ( v1_finset_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_finset_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',cc2_finset_1)).

fof(t29_finset_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_finset_1(k1_relat_1(X1))
      <=> v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t29_finset_1)).

fof(fc13_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k9_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',fc13_finset_1)).

fof(dt_k7_funct_3,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(k7_funct_3(X1,X2))
      & v1_funct_1(k7_funct_3(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',dt_k7_funct_3)).

fof(fc14_finset_1,axiom,(
    ! [X1,X2] :
      ( ( v1_finset_1(X1)
        & v1_finset_1(X2) )
     => v1_finset_1(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',fc14_finset_1)).

fof(t26_finset_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_finset_1(k1_relat_1(X1))
       => v1_finset_1(k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t29_finset_1.p',t26_finset_1)).

fof(c_0_10,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_11,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | r1_tarski(X27,k2_zfmisc_1(k1_relat_1(X27),k2_relat_1(X27))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

fof(c_0_12,plain,(
    ! [X24] :
      ( ~ v1_relat_1(X24)
      | ~ v1_funct_1(X24)
      | k9_relat_1(k9_funct_3(k1_relat_1(X24),k2_relat_1(X24)),X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_funct_3])])).

fof(c_0_13,plain,(
    ! [X22,X23] : k9_funct_3(X22,X23) = k7_funct_3(X22,X23) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_funct_3])).

fof(c_0_14,plain,(
    ! [X44,X45] :
      ( ~ v1_finset_1(X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(X44))
      | v1_finset_1(X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_finset_1])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_finset_1(k1_relat_1(X1))
        <=> v1_finset_1(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t29_finset_1])).

fof(c_0_18,plain,(
    ! [X48,X49] :
      ( ~ v1_relat_1(X48)
      | ~ v1_funct_1(X48)
      | ~ v1_finset_1(X49)
      | v1_finset_1(k9_relat_1(X48,X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc13_finset_1])])).

cnf(c_0_19,plain,
    ( k9_relat_1(k9_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k9_funct_3(X1,X2) = k7_funct_3(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k7_funct_3(X8,X9))
      & v1_funct_1(k7_funct_3(X8,X9)) ) ),
    inference(variable_rename,[status(thm)],[dt_k7_funct_3])).

cnf(c_0_22,plain,
    ( v1_finset_1(X2)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_24,plain,(
    ! [X50,X51] :
      ( ~ v1_finset_1(X50)
      | ~ v1_finset_1(X51)
      | v1_finset_1(k2_zfmisc_1(X50,X51)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc14_finset_1])])).

fof(c_0_25,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_finset_1(k1_relat_1(esk1_0))
      | ~ v1_finset_1(esk1_0) )
    & ( v1_finset_1(k1_relat_1(esk1_0))
      | v1_finset_1(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_26,plain,
    ( v1_finset_1(k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k9_relat_1(k7_funct_3(k1_relat_1(X1),k2_relat_1(X1)),X1) = k1_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( v1_funct_1(k7_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_relat_1(k7_funct_3(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( v1_finset_1(k2_zfmisc_1(X1,X2))
    | ~ v1_finset_1(X1)
    | ~ v1_finset_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | ~ v1_funct_1(X28)
      | ~ v1_finset_1(k1_relat_1(X28))
      | v1_finset_1(k2_relat_1(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_finset_1])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_finset_1(k1_relat_1(esk1_0))
    | ~ v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( v1_finset_1(k1_relat_1(X1))
    | ~ v1_finset_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k2_relat_1(X1))
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( v1_finset_1(k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk1_0))
    | v1_finset_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_finset_1(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_41,plain,
    ( v1_finset_1(X1)
    | ~ v1_finset_1(k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( v1_finset_1(k1_relat_1(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35]),c_0_36])]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
