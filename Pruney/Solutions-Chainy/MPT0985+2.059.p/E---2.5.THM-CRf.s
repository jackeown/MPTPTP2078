%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:41 EST 2020

% Result     : Theorem 0.57s
% Output     : CNFRefutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  120 (6868 expanded)
%              Number of clauses        :   85 (2559 expanded)
%              Number of leaves         :   18 (1757 expanded)
%              Depth                    :   18
%              Number of atoms          :  372 (32960 expanded)
%              Number of equality atoms :   93 (5744 expanded)
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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

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

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,plain,(
    ! [X35] :
      ( ( v1_funct_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( v1_funct_2(X35,k1_relat_1(X35),k2_relat_1(X35))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X35),k2_relat_1(X35))))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_20,plain,(
    ! [X22] :
      ( ( k2_relat_1(X22) = k1_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( k1_relat_1(X22) = k2_relat_1(k2_funct_1(X22))
        | ~ v2_funct_1(X22)
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_21,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | k2_relset_1(X29,X30,X31) = k2_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,esk1_0,esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk3_0)
    & k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_23,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X17,X18] : v1_relat_1(k2_zfmisc_1(X17,X18)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k2_relset_1(esk1_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k1_relset_1(X26,X27,X28) = k1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30,c_0_28]),c_0_31])])).

fof(c_0_38,plain,(
    ! [X32,X33,X34] :
      ( ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X33 = k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X32 = k1_relset_1(X32,X33,X34)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X32 != k1_relset_1(X32,X33,X34)
        | v1_funct_2(X34,X32,X33)
        | X32 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( ~ v1_funct_2(X34,X32,X33)
        | X34 = k1_xboole_0
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( X34 != k1_xboole_0
        | v1_funct_2(X34,X32,X33)
        | X32 = k1_xboole_0
        | X33 != k1_xboole_0
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_39,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_41,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk3_0) = k1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_39,c_0_28])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_45,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

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

fof(c_0_47,plain,(
    ! [X5,X6] :
      ( ~ v1_xboole_0(X5)
      | X5 = X6
      | ~ v1_xboole_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40,c_0_41]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk3_0) = esk1_0
    | k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42,c_0_28]),c_0_43]),c_0_44])])).

cnf(c_0_50,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(k2_funct_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_45,c_0_41])).

fof(c_0_51,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_xboole_0(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_55,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50,c_0_49]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_57,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_28,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_28,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56,c_0_26]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

fof(c_0_64,plain,(
    ! [X21] :
      ( ( v1_relat_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k2_funct_1(X21))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

cnf(c_0_65,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57,c_0_53]),c_0_57]),c_0_58])])).

cnf(c_0_67,negated_conjecture,
    ( v1_xboole_0(esk3_0)
    | k1_xboole_0 != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59,c_0_60]),c_0_58])])).

fof(c_0_68,plain,(
    ! [X36,X37] :
      ( ( v1_funct_1(X37)
        | ~ r1_tarski(k2_relat_1(X37),X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( v1_funct_2(X37,k1_relat_1(X37),X36)
        | ~ r1_tarski(k2_relat_1(X37),X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X37),X36)))
        | ~ r1_tarski(k2_relat_1(X37),X36)
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,X1) = k1_relat_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_39,c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,X1) = k1_relat_1(esk3_0)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_43,c_0_53])).

fof(c_0_71,plain,(
    ! [X9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_72,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_relat_1(k2_funct_1(esk3_0)) ),
    inference(pm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_54,c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(pm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( esk3_0 = X1
    | k1_xboole_0 != esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_53,c_0_67])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_relat_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_80,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_81,negated_conjecture,
    ( k1_xboole_0 = esk2_0
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_73]),c_0_36]),c_0_37])])).

cnf(c_0_82,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_83,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_60,c_0_76])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_relat_1(X1),X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77,c_0_78]),c_0_36]),c_0_37]),c_0_34])])).

fof(c_0_86,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,X4) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_87,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39,c_0_79]),c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( k1_xboole_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81,c_0_82]),c_0_36]),c_0_37])])).

cnf(c_0_89,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(esk3_0,k1_xboole_0,X1)
    | ~ r1_tarski(esk2_0,X1)
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85,c_0_80]),c_0_58])])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | k1_xboole_0 != esk2_0 ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_75]),c_0_87])).

cnf(c_0_93,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_88]),c_0_88])])).

cnf(c_0_94,negated_conjecture,
    ( k1_xboole_0 != esk2_0
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_89,c_0_75])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ r1_tarski(esk2_0,X2)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_90,c_0_53])).

cnf(c_0_96,plain,
    ( r1_tarski(esk2_0,X1) ),
    inference(rw,[status(thm)],[c_0_91,c_0_88])).

cnf(c_0_97,plain,
    ( v1_xboole_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(X1) ),
    inference(pm,[status(thm)],[c_0_36,c_0_53])).

fof(c_0_99,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_funct_1(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X19))
      | v1_funct_1(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

cnf(c_0_100,negated_conjecture,
    ( k1_relat_1(esk2_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_88]),c_0_88])]),c_0_93])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_88]),c_0_88]),c_0_88])]),c_0_93])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(X1,esk2_0,X2)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_88]),c_0_96]),c_0_93]),c_0_97])])).

cnf(c_0_103,negated_conjecture,
    ( v1_funct_1(X1)
    | k1_xboole_0 != esk2_0
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_98,c_0_75]),c_0_58])])).

cnf(c_0_104,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_93]),c_0_93]),c_0_93]),c_0_93]),c_0_100])).

cnf(c_0_106,plain,
    ( k2_zfmisc_1(X1,X2) = esk2_0
    | X1 != esk2_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_88]),c_0_88])).

cnf(c_0_107,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_88])])).

cnf(c_0_109,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_104,c_0_79])).

cnf(c_0_110,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(pm,[status(thm)],[c_0_30,c_0_79])).

cnf(c_0_111,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(esk2_0))
    | ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( ~ v1_xboole_0(k2_funct_1(esk2_0)) ),
    inference(pm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109,c_0_37]),c_0_36])])).

cnf(c_0_114,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(pm,[status(thm)],[c_0_110,c_0_37])).

cnf(c_0_115,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0))
    | ~ v1_relat_1(k2_funct_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59,c_0_111]),c_0_97])]),c_0_112])).

cnf(c_0_116,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_113,c_0_88])).

cnf(c_0_117,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(rw,[status(thm)],[c_0_114,c_0_88])).

cnf(c_0_118,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115,c_0_73]),c_0_116]),c_0_117])])).

cnf(c_0_119,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118,c_0_82]),c_0_116]),c_0_117])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.57/0.73  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.57/0.73  # and selection function NoSelection.
% 0.57/0.73  #
% 0.57/0.73  # Preprocessing time       : 0.028 s
% 0.57/0.73  
% 0.57/0.73  # Proof found!
% 0.57/0.73  # SZS status Theorem
% 0.57/0.73  # SZS output start CNFRefutation
% 0.57/0.73  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.57/0.73  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.57/0.73  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.57/0.73  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.57/0.73  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.57/0.73  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.57/0.73  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.57/0.73  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.57/0.73  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.57/0.73  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 0.57/0.73  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.57/0.73  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.57/0.73  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.57/0.73  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.57/0.73  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.57/0.73  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.57/0.73  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.57/0.73  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.57/0.73  fof(c_0_18, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.57/0.73  fof(c_0_19, plain, ![X35]:(((v1_funct_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(v1_funct_2(X35,k1_relat_1(X35),k2_relat_1(X35))|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X35),k2_relat_1(X35))))|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.57/0.73  fof(c_0_20, plain, ![X22]:((k2_relat_1(X22)=k1_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))&(k1_relat_1(X22)=k2_relat_1(k2_funct_1(X22))|~v2_funct_1(X22)|(~v1_relat_1(X22)|~v1_funct_1(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.57/0.73  fof(c_0_21, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|k2_relset_1(X29,X30,X31)=k2_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.57/0.73  fof(c_0_22, negated_conjecture, (((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,esk1_0,esk2_0))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&((v2_funct_1(esk3_0)&k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0)&(~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.57/0.73  fof(c_0_23, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.57/0.73  fof(c_0_24, plain, ![X17, X18]:v1_relat_1(k2_zfmisc_1(X17,X18)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.57/0.73  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.57/0.73  cnf(c_0_26, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.57/0.73  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.57/0.73  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.73  cnf(c_0_29, negated_conjecture, (k2_relset_1(esk1_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.73  cnf(c_0_30, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.57/0.73  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.57/0.73  fof(c_0_32, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k1_relset_1(X26,X27,X28)=k1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.57/0.73  cnf(c_0_33, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.57/0.73  cnf(c_0_34, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.57/0.73  cnf(c_0_35, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.73  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.73  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_30, c_0_28]), c_0_31])])).
% 0.57/0.73  fof(c_0_38, plain, ![X32, X33, X34]:((((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X33=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&((~v1_funct_2(X34,X32,X33)|X32=k1_relset_1(X32,X33,X34)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X32!=k1_relset_1(X32,X33,X34)|v1_funct_2(X34,X32,X33)|X32!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&((~v1_funct_2(X34,X32,X33)|X34=k1_xboole_0|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))&(X34!=k1_xboole_0|v1_funct_2(X34,X32,X33)|X32=k1_xboole_0|X33!=k1_xboole_0|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.57/0.73  cnf(c_0_39, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.57/0.73  cnf(c_0_40, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k2_relat_1(k2_funct_1(esk3_0)))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.57/0.73  cnf(c_0_41, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.57/0.73  cnf(c_0_42, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.57/0.73  cnf(c_0_43, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk3_0)=k1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_39, c_0_28])).
% 0.57/0.73  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.73  cnf(c_0_45, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.57/0.73  fof(c_0_46, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.57/0.73  fof(c_0_47, plain, ![X5, X6]:(~v1_xboole_0(X5)|X5=X6|~v1_xboole_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.57/0.73  cnf(c_0_48, negated_conjecture, (m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,k1_relat_1(esk3_0))))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_40, c_0_41]), c_0_35]), c_0_36]), c_0_37])])).
% 0.57/0.73  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk3_0)=esk1_0|k1_xboole_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_42, c_0_28]), c_0_43]), c_0_44])])).
% 0.57/0.73  cnf(c_0_50, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(k2_funct_1(X1))|~v1_funct_1(X1)|~v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_45, c_0_41])).
% 0.57/0.73  fof(c_0_51, plain, ![X10, X11]:(~v1_xboole_0(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_xboole_0(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.57/0.73  cnf(c_0_52, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.57/0.73  cnf(c_0_53, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.57/0.73  cnf(c_0_54, negated_conjecture, (~v1_funct_1(k2_funct_1(esk3_0))|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.57/0.73  cnf(c_0_55, negated_conjecture, (k1_xboole_0=esk2_0|m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_48, c_0_49])).
% 0.57/0.73  cnf(c_0_56, negated_conjecture, (k1_xboole_0=esk2_0|v1_funct_2(k2_funct_1(esk3_0),k1_relat_1(k2_funct_1(esk3_0)),esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_50, c_0_49]), c_0_35]), c_0_36]), c_0_37])])).
% 0.57/0.73  cnf(c_0_57, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.57/0.73  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.57/0.73  cnf(c_0_59, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.57/0.73  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_28, c_0_52])).
% 0.57/0.73  cnf(c_0_61, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_28, c_0_53])).
% 0.57/0.73  cnf(c_0_62, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_54, c_0_55])).
% 0.57/0.73  cnf(c_0_63, negated_conjecture, (k1_xboole_0=esk2_0|v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56, c_0_26]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.57/0.73  fof(c_0_64, plain, ![X21]:((v1_relat_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(v1_funct_1(k2_funct_1(X21))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.57/0.73  cnf(c_0_65, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.57/0.73  cnf(c_0_66, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57, c_0_53]), c_0_57]), c_0_58])])).
% 0.57/0.73  cnf(c_0_67, negated_conjecture, (v1_xboole_0(esk3_0)|k1_xboole_0!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59, c_0_60]), c_0_58])])).
% 0.57/0.73  fof(c_0_68, plain, ![X36, X37]:(((v1_funct_1(X37)|~r1_tarski(k2_relat_1(X37),X36)|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(v1_funct_2(X37,k1_relat_1(X37),X36)|~r1_tarski(k2_relat_1(X37),X36)|(~v1_relat_1(X37)|~v1_funct_1(X37))))&(m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X37),X36)))|~r1_tarski(k2_relat_1(X37),X36)|(~v1_relat_1(X37)|~v1_funct_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.57/0.73  cnf(c_0_69, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,X1)=k1_relat_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_39, c_0_61])).
% 0.57/0.73  cnf(c_0_70, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,X1)=k1_relat_1(esk3_0)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_43, c_0_53])).
% 0.57/0.73  fof(c_0_71, plain, ![X9]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X9)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.57/0.73  cnf(c_0_72, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))|~v1_relat_1(k2_funct_1(esk3_0))), inference(pm,[status(thm)],[c_0_62, c_0_63])).
% 0.57/0.73  cnf(c_0_73, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.57/0.73  cnf(c_0_74, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_54, c_0_65])).
% 0.57/0.73  cnf(c_0_75, negated_conjecture, (esk3_0=k1_xboole_0|k1_xboole_0!=esk2_0), inference(pm,[status(thm)],[c_0_66, c_0_67])).
% 0.57/0.73  cnf(c_0_76, negated_conjecture, (esk3_0=X1|k1_xboole_0!=esk2_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_53, c_0_67])).
% 0.57/0.73  cnf(c_0_77, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.57/0.73  cnf(c_0_78, negated_conjecture, (k1_relat_1(esk3_0)=k1_relat_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_69, c_0_70])).
% 0.57/0.73  cnf(c_0_79, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.57/0.73  cnf(c_0_80, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.57/0.73  cnf(c_0_81, negated_conjecture, (k1_xboole_0=esk2_0|~v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_73]), c_0_36]), c_0_37])])).
% 0.57/0.73  cnf(c_0_82, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.57/0.73  cnf(c_0_83, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_74, c_0_75])).
% 0.57/0.73  cnf(c_0_84, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k1_xboole_0!=esk2_0|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_60, c_0_76])).
% 0.57/0.73  cnf(c_0_85, negated_conjecture, (v1_funct_2(esk3_0,k1_relat_1(X1),X2)|~r1_tarski(esk2_0,X2)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_77, c_0_78]), c_0_36]), c_0_37]), c_0_34])])).
% 0.57/0.73  fof(c_0_86, plain, ![X4]:r1_tarski(k1_xboole_0,X4), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.57/0.73  cnf(c_0_87, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_39, c_0_79]), c_0_80])).
% 0.57/0.73  cnf(c_0_88, negated_conjecture, (k1_xboole_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_81, c_0_82]), c_0_36]), c_0_37])])).
% 0.57/0.73  cnf(c_0_89, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(esk3_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_83, c_0_84])).
% 0.57/0.73  cnf(c_0_90, negated_conjecture, (v1_funct_2(esk3_0,k1_xboole_0,X1)|~r1_tarski(esk2_0,X1)|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_85, c_0_80]), c_0_58])])).
% 0.57/0.73  cnf(c_0_91, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 0.57/0.73  cnf(c_0_92, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|k1_xboole_0!=esk2_0), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_75]), c_0_87])).
% 0.57/0.73  cnf(c_0_93, negated_conjecture, (esk3_0=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_88]), c_0_88])])).
% 0.57/0.73  cnf(c_0_94, negated_conjecture, (k1_xboole_0!=esk2_0|~v1_funct_2(k2_funct_1(k1_xboole_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk3_0))|~v1_xboole_0(k2_funct_1(k1_xboole_0))), inference(pm,[status(thm)],[c_0_89, c_0_75])).
% 0.57/0.73  cnf(c_0_95, negated_conjecture, (v1_funct_2(X1,k1_xboole_0,X2)|~r1_tarski(esk2_0,X2)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_90, c_0_53])).
% 0.57/0.73  cnf(c_0_96, plain, (r1_tarski(esk2_0,X1)), inference(rw,[status(thm)],[c_0_91, c_0_88])).
% 0.57/0.73  cnf(c_0_97, plain, (v1_xboole_0(esk2_0)), inference(rw,[status(thm)],[c_0_58, c_0_88])).
% 0.57/0.73  cnf(c_0_98, negated_conjecture, (v1_funct_1(X1)|~v1_xboole_0(esk3_0)|~v1_xboole_0(X1)), inference(pm,[status(thm)],[c_0_36, c_0_53])).
% 0.57/0.73  fof(c_0_99, plain, ![X19, X20]:(~v1_relat_1(X19)|~v1_funct_1(X19)|(~m1_subset_1(X20,k1_zfmisc_1(X19))|v1_funct_1(X20))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.57/0.73  cnf(c_0_100, negated_conjecture, (k1_relat_1(esk2_0)=esk2_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_88]), c_0_88])]), c_0_93])).
% 0.57/0.73  cnf(c_0_101, negated_conjecture, (~v1_funct_2(k2_funct_1(esk2_0),esk2_0,esk1_0)|~v1_funct_1(k2_funct_1(esk2_0))|~v1_xboole_0(k2_funct_1(esk2_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_88]), c_0_88]), c_0_88])]), c_0_93])).
% 0.57/0.73  cnf(c_0_102, negated_conjecture, (v1_funct_2(X1,esk2_0,X2)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_88]), c_0_96]), c_0_93]), c_0_97])])).
% 0.57/0.73  cnf(c_0_103, negated_conjecture, (v1_funct_1(X1)|k1_xboole_0!=esk2_0|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_98, c_0_75]), c_0_58])])).
% 0.57/0.73  cnf(c_0_104, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_99])).
% 0.57/0.73  cnf(c_0_105, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))|~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_93]), c_0_93]), c_0_93]), c_0_93]), c_0_100])).
% 0.57/0.73  cnf(c_0_106, plain, (k2_zfmisc_1(X1,X2)=esk2_0|X1!=esk2_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_88]), c_0_88])).
% 0.57/0.73  cnf(c_0_107, negated_conjecture, (~v1_funct_1(k2_funct_1(esk2_0))|~v1_xboole_0(k2_funct_1(esk2_0))), inference(pm,[status(thm)],[c_0_101, c_0_102])).
% 0.57/0.73  cnf(c_0_108, negated_conjecture, (v1_funct_1(X1)|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_88])])).
% 0.57/0.73  cnf(c_0_109, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_104, c_0_79])).
% 0.57/0.73  cnf(c_0_110, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(pm,[status(thm)],[c_0_30, c_0_79])).
% 0.57/0.73  cnf(c_0_111, negated_conjecture, (m1_subset_1(k2_funct_1(esk2_0),k1_zfmisc_1(esk2_0))|~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(pm,[status(thm)],[c_0_105, c_0_106])).
% 0.57/0.73  cnf(c_0_112, negated_conjecture, (~v1_xboole_0(k2_funct_1(esk2_0))), inference(pm,[status(thm)],[c_0_107, c_0_108])).
% 0.57/0.73  cnf(c_0_113, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_109, c_0_37]), c_0_36])])).
% 0.57/0.73  cnf(c_0_114, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(pm,[status(thm)],[c_0_110, c_0_37])).
% 0.57/0.73  cnf(c_0_115, negated_conjecture, (~v1_funct_1(k2_funct_1(esk2_0))|~v1_relat_1(k2_funct_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_59, c_0_111]), c_0_97])]), c_0_112])).
% 0.57/0.73  cnf(c_0_116, negated_conjecture, (v1_funct_1(esk2_0)), inference(rw,[status(thm)],[c_0_113, c_0_88])).
% 0.57/0.73  cnf(c_0_117, negated_conjecture, (v1_relat_1(esk2_0)), inference(rw,[status(thm)],[c_0_114, c_0_88])).
% 0.57/0.73  cnf(c_0_118, negated_conjecture, (~v1_funct_1(k2_funct_1(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_115, c_0_73]), c_0_116]), c_0_117])])).
% 0.57/0.73  cnf(c_0_119, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_118, c_0_82]), c_0_116]), c_0_117])]), ['proof']).
% 0.57/0.73  # SZS output end CNFRefutation
% 0.57/0.73  # Proof object total steps             : 120
% 0.57/0.73  # Proof object clause steps            : 85
% 0.57/0.73  # Proof object formula steps           : 35
% 0.57/0.73  # Proof object conjectures             : 57
% 0.57/0.73  # Proof object clause conjectures      : 54
% 0.57/0.73  # Proof object formula conjectures     : 3
% 0.57/0.73  # Proof object initial clauses used    : 28
% 0.57/0.73  # Proof object initial formulas used   : 18
% 0.57/0.73  # Proof object generating inferences   : 46
% 0.57/0.73  # Proof object simplifying inferences  : 85
% 0.57/0.73  # Training examples: 0 positive, 0 negative
% 0.57/0.73  # Parsed axioms                        : 20
% 0.57/0.73  # Removed by relevancy pruning/SinE    : 0
% 0.57/0.73  # Initial clauses                      : 39
% 0.57/0.73  # Removed in clause preprocessing      : 2
% 0.57/0.73  # Initial clauses in saturation        : 37
% 0.57/0.73  # Processed clauses                    : 4293
% 0.57/0.73  # ...of these trivial                  : 138
% 0.57/0.73  # ...subsumed                          : 3195
% 0.57/0.73  # ...remaining for further processing  : 960
% 0.57/0.73  # Other redundant clauses eliminated   : 0
% 0.57/0.73  # Clauses deleted for lack of memory   : 0
% 0.57/0.73  # Backward-subsumed                    : 130
% 0.57/0.73  # Backward-rewritten                   : 650
% 0.57/0.73  # Generated clauses                    : 29366
% 0.57/0.73  # ...of the previous two non-trivial   : 26388
% 0.57/0.73  # Contextual simplify-reflections      : 0
% 0.57/0.73  # Paramodulations                      : 29364
% 0.57/0.73  # Factorizations                       : 0
% 0.57/0.73  # Equation resolutions                 : 2
% 0.57/0.73  # Propositional unsat checks           : 0
% 0.57/0.73  #    Propositional check models        : 0
% 0.57/0.73  #    Propositional check unsatisfiable : 0
% 0.57/0.73  #    Propositional clauses             : 0
% 0.57/0.73  #    Propositional clauses after purity: 0
% 0.57/0.73  #    Propositional unsat core size     : 0
% 0.57/0.73  #    Propositional preprocessing time  : 0.000
% 0.57/0.73  #    Propositional encoding time       : 0.000
% 0.57/0.73  #    Propositional solver time         : 0.000
% 0.57/0.73  #    Success case prop preproc time    : 0.000
% 0.57/0.73  #    Success case prop encoding time   : 0.000
% 0.57/0.73  #    Success case prop solver time     : 0.000
% 0.57/0.73  # Current number of processed clauses  : 180
% 0.57/0.73  #    Positive orientable unit clauses  : 16
% 0.57/0.73  #    Positive unorientable unit clauses: 0
% 0.57/0.73  #    Negative unit clauses             : 4
% 0.57/0.73  #    Non-unit-clauses                  : 160
% 0.57/0.73  # Current number of unprocessed clauses: 21741
% 0.57/0.73  # ...number of literals in the above   : 130683
% 0.57/0.73  # Current number of archived formulas  : 0
% 0.57/0.73  # Current number of archived clauses   : 780
% 0.57/0.73  # Clause-clause subsumption calls (NU) : 77554
% 0.57/0.73  # Rec. Clause-clause subsumption calls : 29260
% 0.57/0.73  # Non-unit clause-clause subsumptions  : 3128
% 0.57/0.73  # Unit Clause-clause subsumption calls : 539
% 0.57/0.73  # Rewrite failures with RHS unbound    : 0
% 0.57/0.73  # BW rewrite match attempts            : 21
% 0.57/0.73  # BW rewrite match successes           : 11
% 0.57/0.73  # Condensation attempts                : 0
% 0.57/0.73  # Condensation successes               : 0
% 0.57/0.73  # Termbank termtop insertions          : 208240
% 0.57/0.73  
% 0.57/0.73  # -------------------------------------------------
% 0.57/0.73  # User time                : 0.373 s
% 0.57/0.73  # System time              : 0.021 s
% 0.57/0.73  # Total time               : 0.394 s
% 0.57/0.73  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
