%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:36 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  109 (7448 expanded)
%              Number of clauses        :   76 (2771 expanded)
%              Number of leaves         :   17 (1858 expanded)
%              Depth                    :   18
%              Number of atoms          :  336 (37568 expanded)
%              Number of equality atoms :   80 (6663 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc1_funct_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => v1_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(c_0_17,negated_conjecture,(
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

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_20,plain,(
    ! [X30] :
      ( ( v1_funct_1(X30)
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( v1_funct_2(X30,k1_relat_1(X30),k2_relat_1(X30))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) )
      & ( m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X30),k2_relat_1(X30))))
        | ~ v1_relat_1(X30)
        | ~ v1_funct_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_21,plain,(
    ! [X14] :
      ( ( k2_relat_1(X14) = k1_relat_1(k2_funct_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) )
      & ( k1_relat_1(X14) = k2_relat_1(k2_funct_1(X14))
        | ~ v2_funct_1(X14)
        | ~ v1_relat_1(X14)
        | ~ v1_funct_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_22,plain,(
    ! [X27,X28,X29] :
      ( ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X28 = k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X27 = k1_relset_1(X27,X28,X29)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X27 != k1_relset_1(X27,X28,X29)
        | v1_funct_2(X29,X27,X28)
        | X27 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( ~ v1_funct_2(X29,X27,X28)
        | X29 = k1_xboole_0
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( X29 != k1_xboole_0
        | v1_funct_2(X29,X27,X28)
        | X27 = k1_xboole_0
        | X28 != k1_xboole_0
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_23,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_25,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | v1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_32,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k2_relset_1(X24,X25,X26) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28,c_0_24]),c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_31,c_0_24])).

cnf(c_0_38,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_41,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | X5 = X6
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_42,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),esk1_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_43,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38,c_0_24]),c_0_39])).

cnf(c_0_45,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_40,c_0_27])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_47,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_xboole_0(X18)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | v1_xboole_0(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

fof(c_0_48,plain,(
    ! [X11] :
      ( ( k1_relat_1(X11) != k1_xboole_0
        | k2_relat_1(X11) = k1_xboole_0
        | ~ v1_relat_1(X11) )
      & ( k2_relat_1(X11) != k1_xboole_0
        | k1_relat_1(X11) = k1_xboole_0
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_50,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_51,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45,c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_24,c_0_46])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26,c_0_44]),c_0_36]),c_0_37])])).

cnf(c_0_55,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51,c_0_43]),c_0_44]),c_0_35]),c_0_36]),c_0_37])])).

fof(c_0_58,plain,(
    ! [X13] :
      ( ( v1_relat_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) )
      & ( v1_funct_1(k2_funct_1(X13))
        | ~ v1_relat_1(X13)
        | ~ v1_funct_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_59,plain,(
    ! [X31,X32] :
      ( ( v1_funct_1(X32)
        | ~ r1_tarski(k2_relat_1(X32),X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_2(X32,k1_relat_1(X32),X31)
        | ~ r1_tarski(k2_relat_1(X32),X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X32),X31)))
        | ~ r1_tarski(k2_relat_1(X32),X31)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_60,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,X1) = k1_relat_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_23,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,X1) = k1_relat_1(esk3_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_29,c_0_46])).

cnf(c_0_62,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(k1_relat_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_37]),c_0_44])).

cnf(c_0_66,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_68,plain,(
    ! [X7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_69,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relat_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_71,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_46]),c_0_62]),c_0_63])])).

cnf(c_0_72,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64,c_0_65]),c_0_63])])).

cnf(c_0_73,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_36]),c_0_37])])).

cnf(c_0_74,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_xboole_0(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_49,c_0_46])).

cnf(c_0_76,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_relat_1(X1),X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69,c_0_70]),c_0_36]),c_0_37]),c_0_44])])).

cnf(c_0_78,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_79,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_80,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73,c_0_74]),c_0_36]),c_0_37])])).

cnf(c_0_82,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_76]),c_0_63])])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ r1_tarski(esk2_0,X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_78]),c_0_63])])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_81])])).

cnf(c_0_86,negated_conjecture,
    ( v2_funct_1(k1_xboole_0)
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_35,c_0_80])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_36,c_0_80])).

cnf(c_0_88,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_31,c_0_76])).

cnf(c_0_89,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_82,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_83,c_0_46])).

cnf(c_0_91,plain,
    ( r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_84,c_0_81])).

cnf(c_0_92,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_81])).

cnf(c_0_93,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_81]),c_0_81])]),c_0_85])).

cnf(c_0_94,negated_conjecture,
    ( v2_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_81]),c_0_81])])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_81]),c_0_81])])).

cnf(c_0_96,plain,
    ( v1_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_81])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_81]),c_0_81])]),c_0_85]),c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_2(X1,esk2_0,X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_81]),c_0_91]),c_0_85]),c_0_92])])).

fof(c_0_99,plain,(
    ! [X12] :
      ( ~ v1_xboole_0(X12)
      | v1_funct_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk2_0)),esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33,c_0_93]),c_0_94]),c_0_95]),c_0_96])])).

cnf(c_0_101,plain,
    ( k2_relat_1(esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_81]),c_0_81])).

cnf(c_0_102,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_103,plain,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100,c_0_43]),c_0_101]),c_0_94]),c_0_95]),c_0_96])])).

cnf(c_0_105,negated_conjecture,
    ( ~ v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_102,c_0_103])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_104]),c_0_92])]),c_0_105])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106,c_0_67]),c_0_95]),c_0_96])])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107,c_0_74]),c_0_95]),c_0_96])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.42/0.63  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.42/0.63  # and selection function NoSelection.
% 0.42/0.63  #
% 0.42/0.63  # Preprocessing time       : 0.028 s
% 0.42/0.63  
% 0.42/0.63  # Proof found!
% 0.42/0.63  # SZS status Theorem
% 0.42/0.63  # SZS output start CNFRefutation
% 0.42/0.63  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.42/0.63  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.42/0.63  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.42/0.63  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.42/0.63  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.42/0.63  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.42/0.63  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.42/0.63  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.42/0.63  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.42/0.63  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 0.42/0.63  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.42/0.63  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.42/0.63  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.42/0.63  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.42/0.63  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.42/0.63  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.42/0.63  fof(cc1_funct_1, axiom, ![X1]:(v1_xboole_0(X1)=>v1_funct_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 0.42/0.63  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.42/0.63  fof(c_0_18, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.42/0.63  fof(c_0_19, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.42/0.63  fof(c_0_20, plain, ![X30]:(((v1_funct_1(X30)|(~v1_relat_1(X30)|~v1_funct_1(X30)))&(v1_funct_2(X30,k1_relat_1(X30),k2_relat_1(X30))|(~v1_relat_1(X30)|~v1_funct_1(X30))))&(m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X30),k2_relat_1(X30))))|(~v1_relat_1(X30)|~v1_funct_1(X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.42/0.63  fof(c_0_21, plain, ![X14]:((k2_relat_1(X14)=k1_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))&(k1_relat_1(X14)=k2_relat_1(k2_funct_1(X14))|~v2_funct_1(X14)|(~v1_relat_1(X14)|~v1_funct_1(X14)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.42/0.63  fof(c_0_22, plain, ![X27, X28, X29]:((((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X28=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&((~v1_funct_2(X29,X27,X28)|X27=k1_relset_1(X27,X28,X29)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X27!=k1_relset_1(X27,X28,X29)|v1_funct_2(X29,X27,X28)|X27!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))))&((~v1_funct_2(X29,X27,X28)|X29=k1_xboole_0|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(X29!=k1_xboole_0|v1_funct_2(X29,X27,X28)|X27=k1_xboole_0|X28!=k1_xboole_0|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.42/0.63  cnf(c_0_23, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.42/0.63  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.63  fof(c_0_25, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|v1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.42/0.63  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.63  cnf(c_0_27, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.63  cnf(c_0_28, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.42/0.63  cnf(c_0_29, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_23, c_0_24])).
% 0.42/0.63  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.63  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.42/0.63  fof(c_0_32, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k2_relset_1(X24,X25,X26)=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.42/0.63  cnf(c_0_33, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_26, c_0_27])).
% 0.42/0.63  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|k1_xboole_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_28, c_0_24]), c_0_29]), c_0_30])])).
% 0.42/0.63  cnf(c_0_35, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.63  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.63  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_31, c_0_24])).
% 0.42/0.63  cnf(c_0_38, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.42/0.63  cnf(c_0_39, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.63  cnf(c_0_40, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.42/0.63  fof(c_0_41, plain, ![X5, X6]:(~v1_xboole_0(X5)|X5=X6|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.42/0.63  cnf(c_0_42, negated_conjecture, (k1_xboole_0=esk2_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk3_0)),esk1_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.42/0.63  cnf(c_0_43, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.42/0.63  cnf(c_0_44, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38, c_0_24]), c_0_39])).
% 0.42/0.63  cnf(c_0_45, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_40, c_0_27])).
% 0.42/0.63  cnf(c_0_46, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.42/0.63  fof(c_0_47, plain, ![X18, X19, X20]:(~v1_xboole_0(X18)|(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|v1_xboole_0(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.42/0.63  fof(c_0_48, plain, ![X11]:((k1_relat_1(X11)!=k1_xboole_0|k2_relat_1(X11)=k1_xboole_0|~v1_relat_1(X11))&(k2_relat_1(X11)!=k1_xboole_0|k1_relat_1(X11)=k1_xboole_0|~v1_relat_1(X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.42/0.63  cnf(c_0_49, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.42/0.63  cnf(c_0_50, negated_conjecture, (k1_xboole_0=esk2_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_35]), c_0_36]), c_0_37])])).
% 0.42/0.63  cnf(c_0_51, negated_conjecture, (k1_xboole_0=esk2_0|v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_45, c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.42/0.63  cnf(c_0_52, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_24, c_0_46])).
% 0.42/0.63  cnf(c_0_53, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.42/0.63  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk3_0),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_26, c_0_44]), c_0_36]), c_0_37])])).
% 0.42/0.63  cnf(c_0_55, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.42/0.63  cnf(c_0_56, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_49, c_0_50])).
% 0.42/0.63  cnf(c_0_57, negated_conjecture, (k1_xboole_0=esk2_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_51, c_0_43]), c_0_44]), c_0_35]), c_0_36]), c_0_37])])).
% 0.42/0.63  fof(c_0_58, plain, ![X13]:((v1_relat_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))&(v1_funct_1(k2_funct_1(X13))|(~v1_relat_1(X13)|~v1_funct_1(X13)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.42/0.63  fof(c_0_59, plain, ![X31, X32]:(((v1_funct_1(X32)|~r1_tarski(k2_relat_1(X32),X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_2(X32,k1_relat_1(X32),X31)|~r1_tarski(k2_relat_1(X32),X31)|(~v1_relat_1(X32)|~v1_funct_1(X32))))&(m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X32),X31)))|~r1_tarski(k2_relat_1(X32),X31)|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.42/0.63  cnf(c_0_60, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,X1)=k1_relat_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_23, c_0_52])).
% 0.42/0.63  cnf(c_0_61, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,X1)=k1_relat_1(esk3_0)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_29, c_0_46])).
% 0.42/0.63  cnf(c_0_62, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.42/0.63  cnf(c_0_63, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.42/0.63  cnf(c_0_64, negated_conjecture, (v1_xboole_0(esk3_0)|~v1_xboole_0(k1_relat_1(esk3_0))), inference(pm,[status(thm)],[c_0_53, c_0_54])).
% 0.42/0.63  cnf(c_0_65, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|k1_xboole_0!=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_37]), c_0_44])).
% 0.42/0.63  cnf(c_0_66, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_56, c_0_57])).
% 0.42/0.63  cnf(c_0_67, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.42/0.63  fof(c_0_68, plain, ![X7]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.42/0.63  cnf(c_0_69, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.42/0.63  cnf(c_0_70, negated_conjecture, (k1_relat_1(esk3_0)=k1_relat_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.42/0.63  cnf(c_0_71, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_46]), c_0_62]), c_0_63])])).
% 0.42/0.63  cnf(c_0_72, negated_conjecture, (v1_xboole_0(esk3_0)|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64, c_0_65]), c_0_63])])).
% 0.42/0.63  cnf(c_0_73, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_36]), c_0_37])])).
% 0.42/0.63  cnf(c_0_74, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.42/0.63  cnf(c_0_75, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_xboole_0(k2_funct_1(esk3_0))|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_49, c_0_46])).
% 0.42/0.63  cnf(c_0_76, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.42/0.63  cnf(c_0_77, negated_conjecture, (v1_funct_2(esk3_0,k1_relat_1(X1),X2)|~r1_tarski(esk2_0,X2)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_69, c_0_70]), c_0_36]), c_0_37]), c_0_44])])).
% 0.42/0.63  cnf(c_0_78, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.42/0.63  fof(c_0_79, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.42/0.63  cnf(c_0_80, negated_conjecture, (esk3_0=k1_xboole_0|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_71, c_0_72])).
% 0.42/0.63  cnf(c_0_81, negated_conjecture, (k1_xboole_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_73, c_0_74]), c_0_36]), c_0_37])])).
% 0.42/0.63  cnf(c_0_82, negated_conjecture, (~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_76]), c_0_63])])).
% 0.42/0.63  cnf(c_0_83, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,X1)|~r1_tarski(esk2_0,X1)|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_78]), c_0_63])])).
% 0.42/0.63  cnf(c_0_84, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.42/0.63  cnf(c_0_85, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_81])])).
% 0.42/0.63  cnf(c_0_86, negated_conjecture, (v2_funct_1(k1_xboole_0)|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_35, c_0_80])).
% 0.42/0.63  cnf(c_0_87, negated_conjecture, (v1_funct_1(k1_xboole_0)|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_36, c_0_80])).
% 0.42/0.63  cnf(c_0_88, plain, (v1_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_31, c_0_76])).
% 0.42/0.63  cnf(c_0_89, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(k1_xboole_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_82, c_0_80])).
% 0.42/0.63  cnf(c_0_90, negated_conjecture, (v1_funct_2(X1,k1_xboole_0,X2)|~r1_tarski(esk2_0,X2)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_83, c_0_46])).
% 0.42/0.63  cnf(c_0_91, plain, (r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[c_0_84, c_0_81])).
% 0.42/0.63  cnf(c_0_92, plain, (v1_xboole_0(esk2_0)), inference(rw,[status(thm)],[c_0_63, c_0_81])).
% 0.42/0.63  cnf(c_0_93, negated_conjecture, (k1_relat_1(esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_81]), c_0_81])]), c_0_85])).
% 0.42/0.63  cnf(c_0_94, negated_conjecture, (v2_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_81]), c_0_81])])).
% 0.42/0.63  cnf(c_0_95, negated_conjecture, (v1_funct_1(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_81]), c_0_81])])).
% 0.42/0.63  cnf(c_0_96, plain, (v1_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_88, c_0_81])).
% 0.42/0.63  cnf(c_0_97, negated_conjecture, (~v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk2_0))|~v1_xboole_0(k2_funct_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_81]), c_0_81])]), c_0_85]), c_0_85])).
% 0.42/0.63  cnf(c_0_98, negated_conjecture, (v1_funct_2(X1,esk2_0,X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_81]), c_0_91]), c_0_85]), c_0_92])])).
% 0.42/0.63  fof(c_0_99, plain, ![X12]:(~v1_xboole_0(X12)|v1_funct_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_1])])).
% 0.42/0.63  cnf(c_0_100, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk2_0)),esk2_0)))|~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33, c_0_93]), c_0_94]), c_0_95]), c_0_96])])).
% 0.42/0.63  cnf(c_0_101, plain, (k2_relat_1(esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_81]), c_0_81])).
% 0.42/0.63  cnf(c_0_102, negated_conjecture, (~v1_funct_1(k2_funct_1(esk2_0))|~v1_xboole_0(k2_funct_1(esk2_0))), inference(pm,[status(thm)],[c_0_97, c_0_98])).
% 0.42/0.63  cnf(c_0_103, plain, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.42/0.63  cnf(c_0_104, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_100, c_0_43]), c_0_101]), c_0_94]), c_0_95]), c_0_96])])).
% 0.42/0.63  cnf(c_0_105, negated_conjecture, (~v1_xboole_0(k2_funct_1(esk2_0))), inference(pm,[status(thm)],[c_0_102, c_0_103])).
% 0.42/0.63  cnf(c_0_106, negated_conjecture, (~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_104]), c_0_92])]), c_0_105])).
% 0.42/0.63  cnf(c_0_107, negated_conjecture, (~v1_funct_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_106, c_0_67]), c_0_95]), c_0_96])])).
% 0.42/0.63  cnf(c_0_108, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_107, c_0_74]), c_0_95]), c_0_96])]), ['proof']).
% 0.42/0.63  # SZS output end CNFRefutation
% 0.42/0.63  # Proof object total steps             : 109
% 0.42/0.63  # Proof object clause steps            : 76
% 0.42/0.63  # Proof object formula steps           : 33
% 0.42/0.63  # Proof object conjectures             : 51
% 0.42/0.63  # Proof object clause conjectures      : 48
% 0.42/0.63  # Proof object formula conjectures     : 3
% 0.42/0.63  # Proof object initial clauses used    : 26
% 0.42/0.63  # Proof object initial formulas used   : 17
% 0.42/0.63  # Proof object generating inferences   : 40
% 0.42/0.63  # Proof object simplifying inferences  : 91
% 0.42/0.63  # Training examples: 0 positive, 0 negative
% 0.42/0.63  # Parsed axioms                        : 18
% 0.42/0.63  # Removed by relevancy pruning/SinE    : 0
% 0.42/0.63  # Initial clauses                      : 36
% 0.42/0.63  # Removed in clause preprocessing      : 2
% 0.42/0.63  # Initial clauses in saturation        : 34
% 0.42/0.63  # Processed clauses                    : 2748
% 0.42/0.63  # ...of these trivial                  : 95
% 0.42/0.63  # ...subsumed                          : 1914
% 0.42/0.63  # ...remaining for further processing  : 739
% 0.42/0.63  # Other redundant clauses eliminated   : 0
% 0.42/0.63  # Clauses deleted for lack of memory   : 0
% 0.42/0.63  # Backward-subsumed                    : 114
% 0.42/0.63  # Backward-rewritten                   : 494
% 0.42/0.63  # Generated clauses                    : 17745
% 0.42/0.63  # ...of the previous two non-trivial   : 16359
% 0.42/0.63  # Contextual simplify-reflections      : 0
% 0.42/0.63  # Paramodulations                      : 17745
% 0.42/0.63  # Factorizations                       : 0
% 0.42/0.63  # Equation resolutions                 : 0
% 0.42/0.63  # Propositional unsat checks           : 0
% 0.42/0.63  #    Propositional check models        : 0
% 0.42/0.63  #    Propositional check unsatisfiable : 0
% 0.42/0.63  #    Propositional clauses             : 0
% 0.42/0.63  #    Propositional clauses after purity: 0
% 0.42/0.63  #    Propositional unsat core size     : 0
% 0.42/0.63  #    Propositional preprocessing time  : 0.000
% 0.42/0.63  #    Propositional encoding time       : 0.000
% 0.42/0.63  #    Propositional solver time         : 0.000
% 0.42/0.63  #    Success case prop preproc time    : 0.000
% 0.42/0.63  #    Success case prop encoding time   : 0.000
% 0.42/0.63  #    Success case prop solver time     : 0.000
% 0.42/0.63  # Current number of processed clauses  : 131
% 0.42/0.63  #    Positive orientable unit clauses  : 15
% 0.42/0.63  #    Positive unorientable unit clauses: 0
% 0.42/0.63  #    Negative unit clauses             : 4
% 0.42/0.63  #    Non-unit-clauses                  : 112
% 0.42/0.63  # Current number of unprocessed clauses: 13457
% 0.42/0.63  # ...number of literals in the above   : 87059
% 0.42/0.63  # Current number of archived formulas  : 0
% 0.42/0.63  # Current number of archived clauses   : 608
% 0.42/0.63  # Clause-clause subsumption calls (NU) : 40689
% 0.42/0.63  # Rec. Clause-clause subsumption calls : 14385
% 0.42/0.63  # Non-unit clause-clause subsumptions  : 1960
% 0.42/0.63  # Unit Clause-clause subsumption calls : 482
% 0.42/0.63  # Rewrite failures with RHS unbound    : 0
% 0.42/0.63  # BW rewrite match attempts            : 17
% 0.42/0.63  # BW rewrite match successes           : 7
% 0.42/0.63  # Condensation attempts                : 0
% 0.42/0.63  # Condensation successes               : 0
% 0.42/0.63  # Termbank termtop insertions          : 134332
% 0.42/0.63  
% 0.42/0.63  # -------------------------------------------------
% 0.42/0.63  # User time                : 0.277 s
% 0.42/0.63  # System time              : 0.013 s
% 0.42/0.63  # Total time               : 0.290 s
% 0.42/0.63  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
