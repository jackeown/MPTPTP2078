%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:21 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 (11624 expanded)
%              Number of clauses        :   91 (4830 expanded)
%              Number of leaves         :   15 (2909 expanded)
%              Depth                    :   34
%              Number of atoms          :  385 (53669 expanded)
%              Number of equality atoms :  164 (15978 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t9_funct_2,conjecture,(
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

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

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t218_relat_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v5_relat_1(X3,X1) )
         => v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(c_0_15,plain,(
    ! [X10,X11] :
      ( ( k2_zfmisc_1(X10,X11) != k1_xboole_0
        | X10 = k1_xboole_0
        | X11 = k1_xboole_0 )
      & ( X10 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X10,X11) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X2,X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t9_funct_2])).

fof(c_0_17,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_18,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & r1_tarski(esk4_0,esk5_0)
    & ( esk4_0 != k1_xboole_0
      | esk3_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk6_0)
      | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
      | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ( ~ v4_relat_1(X18,X17)
        | r1_tarski(k1_relat_1(X18),X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(k1_relat_1(X18),X17)
        | v4_relat_1(X18,X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_22,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X45,X46,X47] :
      ( ( ~ v1_funct_2(X47,X45,X46)
        | X45 = k1_relset_1(X45,X46,X47)
        | X46 = k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X45 != k1_relset_1(X45,X46,X47)
        | v1_funct_2(X47,X45,X46)
        | X46 = k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ v1_funct_2(X47,X45,X46)
        | X45 = k1_relset_1(X45,X46,X47)
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X45 != k1_relset_1(X45,X46,X47)
        | v1_funct_2(X47,X45,X46)
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ v1_funct_2(X47,X45,X46)
        | X47 = k1_xboole_0
        | X45 = k1_xboole_0
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X47 != k1_xboole_0
        | v1_funct_2(X47,X45,X46)
        | X45 = k1_xboole_0
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_25,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | v1_relat_1(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_28,plain,(
    ! [X21,X22] : v1_relat_1(k2_zfmisc_1(X21,X22)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_29,plain,(
    ! [X48] :
      ( ( v1_funct_1(X48)
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( v1_funct_2(X48,k1_relat_1(X48),k2_relat_1(X48))
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) )
      & ( m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X48),k2_relat_1(X48))))
        | ~ v1_relat_1(X48)
        | ~ v1_funct_1(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_30,plain,(
    ! [X26] :
      ( ( k1_relat_1(X26) != k1_xboole_0
        | k2_relat_1(X26) = k1_xboole_0
        | ~ v1_relat_1(X26) )
      & ( k2_relat_1(X26) != k1_xboole_0
        | k1_relat_1(X26) = k1_xboole_0
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_33,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(esk3_0,esk4_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_34]),c_0_35])])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_26]),c_0_37])])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42])])).

fof(c_0_47,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,X1)
    | k1_relat_1(esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(esk3_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_41])).

fof(c_0_51,plain,(
    ! [X19,X20] :
      ( ( ~ v5_relat_1(X20,X19)
        | r1_tarski(k2_relat_1(X20),X19)
        | ~ v1_relat_1(X20) )
      & ( ~ r1_tarski(k2_relat_1(X20),X19)
        | v5_relat_1(X20,X19)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_52,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = esk3_0
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_55,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_56,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k2_relat_1(X1) = esk3_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v5_relat_1(X1,esk3_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(X1) = esk3_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0
    | k1_relat_1(esk6_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_46]),c_0_42])])).

cnf(c_0_61,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk6_0),esk3_0)))
    | k1_relat_1(esk6_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_60]),c_0_44]),c_0_42])])).

fof(c_0_62,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_41])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | v5_relat_1(esk6_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_63])).

cnf(c_0_66,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_64])).

cnf(c_0_67,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_68,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk3_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_65]),c_0_42])])).

fof(c_0_69,plain,(
    ! [X35,X36,X37] :
      ( ~ v1_relat_1(X37)
      | ~ r1_tarski(k1_relat_1(X37),X35)
      | ~ r1_tarski(k2_relat_1(X37),X36)
      | m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_70,negated_conjecture,
    ( v4_relat_1(esk6_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_26])).

cnf(c_0_71,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v5_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_54])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_42])])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_70]),c_0_42])])).

cnf(c_0_75,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_58])).

cnf(c_0_76,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_72]),c_0_56]),c_0_44]),c_0_42])])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ r1_tarski(k2_relat_1(esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_42])])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_72]),c_0_42]),c_0_64])])).

cnf(c_0_79,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_42])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_1(esk6_0)
    | ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_81,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | k1_relat_1(esk6_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_39]),c_0_64]),c_0_42])])).

cnf(c_0_83,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_64])])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_44])])).

cnf(c_0_85,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_79]),c_0_64])])).

cnf(c_0_86,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | k1_relset_1(esk3_0,X1,esk6_0) != esk3_0
    | k1_relat_1(esk6_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( k1_relset_1(X1,X2,esk6_0) = k1_relat_1(esk6_0)
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v1_funct_2(esk6_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_72]),c_0_41])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_91,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_92,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_66])).

cnf(c_0_93,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_40])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))
    | esk3_0 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_92]),c_0_23])).

fof(c_0_95,plain,(
    ! [X23,X24,X25] :
      ( ~ r1_tarski(X23,X24)
      | ~ v1_relat_1(X25)
      | ~ v5_relat_1(X25,X23)
      | v5_relat_1(X25,X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t218_relat_1])])])).

cnf(c_0_96,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_42])])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_54]),c_0_42])])).

cnf(c_0_98,plain,
    ( v5_relat_1(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ v5_relat_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | esk3_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk6_0),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_96]),c_0_42]),c_0_64])])).

cnf(c_0_100,negated_conjecture,
    ( k2_relat_1(esk6_0) = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_94]),c_0_42])])).

cnf(c_0_101,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( v5_relat_1(X1,esk5_0)
    | ~ v5_relat_1(X1,esk4_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_90])).

cnf(c_0_103,negated_conjecture,
    ( v5_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_64])])).

cnf(c_0_105,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | k1_relset_1(esk3_0,X1,esk6_0) != esk3_0
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_81,c_0_97])).

cnf(c_0_106,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_103]),c_0_42])])).

cnf(c_0_107,negated_conjecture,
    ( k1_relset_1(esk3_0,X1,esk6_0) = k1_relat_1(esk6_0)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_97])).

cnf(c_0_108,negated_conjecture,
    ( k1_relset_1(X1,X2,esk6_0) = k1_relat_1(esk6_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_25,c_0_104])).

cnf(c_0_109,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_relset_1(esk3_0,esk5_0,esk6_0) != esk3_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_102]),c_0_103]),c_0_42])]),c_0_106])).

cnf(c_0_110,negated_conjecture,
    ( k1_relset_1(esk3_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_102]),c_0_103]),c_0_42])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_2(esk6_0,esk3_0,esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_101,c_0_58])).

cnf(c_0_112,negated_conjecture,
    ( X1 = k1_xboole_0
    | v1_funct_2(esk6_0,esk3_0,X1)
    | k1_relat_1(esk6_0) != esk3_0
    | esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_108]),c_0_96])).

cnf(c_0_113,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_relat_1(esk6_0) != esk3_0 ),
    inference(rw,[status(thm)],[c_0_109,c_0_110])).

cnf(c_0_114,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | k1_relat_1(esk6_0) != esk3_0
    | esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_94])).

cnf(c_0_115,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_113,c_0_41])).

cnf(c_0_116,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_114,c_0_96])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_92])).

cnf(c_0_118,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk4_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_119,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_115]),c_0_66])).

cnf(c_0_120,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_116]),c_0_23]),c_0_94]),c_0_117])).

cnf(c_0_121,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_119])]),c_0_120]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:29:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.41  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 0.19/0.41  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.41  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.41  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.41  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.19/0.41  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.41  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.19/0.41  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.19/0.41  fof(t218_relat_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>![X3]:((v1_relat_1(X3)&v5_relat_1(X3,X1))=>v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t218_relat_1)).
% 0.19/0.41  fof(c_0_15, plain, ![X10, X11]:((k2_zfmisc_1(X10,X11)!=k1_xboole_0|(X10=k1_xboole_0|X11=k1_xboole_0))&((X10!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0)&(X11!=k1_xboole_0|k2_zfmisc_1(X10,X11)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.41  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.19/0.41  fof(c_0_17, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.41  cnf(c_0_18, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  fof(c_0_19, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.41  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,esk4_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&(r1_tarski(esk4_0,esk5_0)&((esk4_0!=k1_xboole_0|esk3_0=k1_xboole_0)&(~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.41  fof(c_0_21, plain, ![X17, X18]:((~v4_relat_1(X18,X17)|r1_tarski(k1_relat_1(X18),X17)|~v1_relat_1(X18))&(~r1_tarski(k1_relat_1(X18),X17)|v4_relat_1(X18,X17)|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.41  cnf(c_0_22, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  cnf(c_0_23, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_18])).
% 0.19/0.41  fof(c_0_24, plain, ![X45, X46, X47]:((((~v1_funct_2(X47,X45,X46)|X45=k1_relset_1(X45,X46,X47)|X46=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X45!=k1_relset_1(X45,X46,X47)|v1_funct_2(X47,X45,X46)|X46=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&((~v1_funct_2(X47,X45,X46)|X45=k1_relset_1(X45,X46,X47)|X45!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X45!=k1_relset_1(X45,X46,X47)|v1_funct_2(X47,X45,X46)|X45!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))))&((~v1_funct_2(X47,X45,X46)|X47=k1_xboole_0|X45=k1_xboole_0|X46!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X47!=k1_xboole_0|v1_funct_2(X47,X45,X46)|X45=k1_xboole_0|X46!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.41  cnf(c_0_25, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  fof(c_0_27, plain, ![X15, X16]:(~v1_relat_1(X15)|(~m1_subset_1(X16,k1_zfmisc_1(X15))|v1_relat_1(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.41  fof(c_0_28, plain, ![X21, X22]:v1_relat_1(k2_zfmisc_1(X21,X22)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.41  fof(c_0_29, plain, ![X48]:(((v1_funct_1(X48)|(~v1_relat_1(X48)|~v1_funct_1(X48)))&(v1_funct_2(X48,k1_relat_1(X48),k2_relat_1(X48))|(~v1_relat_1(X48)|~v1_funct_1(X48))))&(m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X48),k2_relat_1(X48))))|(~v1_relat_1(X48)|~v1_funct_1(X48)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.19/0.41  fof(c_0_30, plain, ![X26]:((k1_relat_1(X26)!=k1_xboole_0|k2_relat_1(X26)=k1_xboole_0|~v1_relat_1(X26))&(k2_relat_1(X26)!=k1_xboole_0|k1_relat_1(X26)=k1_xboole_0|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.19/0.41  cnf(c_0_31, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_32, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.41  cnf(c_0_33, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.41  cnf(c_0_34, negated_conjecture, (k1_relset_1(esk3_0,esk4_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.41  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_36, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_37, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.41  cnf(c_0_39, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.41  cnf(c_0_40, plain, (r1_tarski(k1_relat_1(X1),X2)|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_34]), c_0_35])])).
% 0.19/0.41  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_26]), c_0_37])])).
% 0.19/0.41  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_23])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.19/0.42  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|k1_relat_1(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_42])])).
% 0.19/0.42  fof(c_0_47, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.42  cnf(c_0_48, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,X1)|k1_relat_1(esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.42  cnf(c_0_49, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(esk3_0,X1)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_41])).
% 0.19/0.42  fof(c_0_51, plain, ![X19, X20]:((~v5_relat_1(X20,X19)|r1_tarski(k2_relat_1(X20),X19)|~v1_relat_1(X20))&(~r1_tarski(k2_relat_1(X20),X19)|v5_relat_1(X20,X19)|~v1_relat_1(X20))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.42  cnf(c_0_52, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_53, negated_conjecture, (esk4_0=k1_xboole_0|X1=esk3_0|esk3_0!=k1_xboole_0|~r1_tarski(X1,esk3_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.42  cnf(c_0_54, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_55, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.42  cnf(c_0_56, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_52])).
% 0.19/0.42  cnf(c_0_57, negated_conjecture, (k2_relat_1(X1)=esk3_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0|~v5_relat_1(X1,esk3_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.42  cnf(c_0_58, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (k2_relat_1(X1)=esk3_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.42  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk6_0)=esk3_0|esk4_0=k1_xboole_0|k1_relat_1(esk6_0)!=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_46]), c_0_42])])).
% 0.19/0.42  cnf(c_0_61, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk6_0),esk3_0)))|k1_relat_1(esk6_0)!=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_60]), c_0_44]), c_0_42])])).
% 0.19/0.42  fof(c_0_62, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.19/0.42  cnf(c_0_63, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_41])).
% 0.19/0.42  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (esk4_0=k1_xboole_0|v5_relat_1(esk6_0,esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_63])).
% 0.19/0.42  cnf(c_0_66, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_64])).
% 0.19/0.42  cnf(c_0_67, plain, (k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.42  cnf(c_0_68, negated_conjecture, (k2_relat_1(esk6_0)=esk3_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_65]), c_0_42])])).
% 0.19/0.42  fof(c_0_69, plain, ![X35, X36, X37]:(~v1_relat_1(X37)|(~r1_tarski(k1_relat_1(X37),X35)|~r1_tarski(k2_relat_1(X37),X36)|m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.19/0.42  cnf(c_0_70, negated_conjecture, (v4_relat_1(esk6_0,esk3_0)), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 0.19/0.42  cnf(c_0_71, plain, (k2_relat_1(X1)=k1_xboole_0|~v5_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_66, c_0_54])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_42])])).
% 0.19/0.42  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (r1_tarski(k1_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_70]), c_0_42])])).
% 0.19/0.42  cnf(c_0_75, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_71, c_0_58])).
% 0.19/0.42  cnf(c_0_76, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_72]), c_0_56]), c_0_44]), c_0_42])])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~r1_tarski(k2_relat_1(esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_42])])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|esk3_0!=k1_xboole_0|~r1_tarski(k2_relat_1(esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_72]), c_0_42]), c_0_64])])).
% 0.19/0.42  cnf(c_0_79, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_42])])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (~v1_funct_1(esk6_0)|~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_81, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|k1_relat_1(esk6_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_39]), c_0_64]), c_0_42])])).
% 0.19/0.42  cnf(c_0_83, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_64])])).
% 0.19/0.42  cnf(c_0_84, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_44])])).
% 0.19/0.42  cnf(c_0_85, negated_conjecture, (esk4_0=k1_xboole_0|m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_79]), c_0_64])])).
% 0.19/0.42  cnf(c_0_86, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|k1_relset_1(esk3_0,X1,esk6_0)!=esk3_0|k1_relat_1(esk6_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.19/0.42  cnf(c_0_87, negated_conjecture, (k1_relset_1(X1,X2,esk6_0)=k1_relat_1(esk6_0)|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_83])).
% 0.19/0.42  cnf(c_0_88, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0|~v1_funct_2(esk6_0,esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.42  cnf(c_0_89, negated_conjecture, (esk4_0=k1_xboole_0|X1=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_72]), c_0_41])).
% 0.19/0.42  cnf(c_0_90, negated_conjecture, (r1_tarski(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_91, negated_conjecture, (esk5_0=k1_xboole_0|esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.42  cnf(c_0_92, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_66])).
% 0.19/0.42  cnf(c_0_93, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_66, c_0_40])).
% 0.19/0.42  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))|esk3_0!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_92]), c_0_23])).
% 0.19/0.42  fof(c_0_95, plain, ![X23, X24, X25]:(~r1_tarski(X23,X24)|(~v1_relat_1(X25)|~v5_relat_1(X25,X23)|v5_relat_1(X25,X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t218_relat_1])])])).
% 0.19/0.42  cnf(c_0_96, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_42])])).
% 0.19/0.42  cnf(c_0_97, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))|~v5_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_54]), c_0_42])])).
% 0.19/0.42  cnf(c_0_98, plain, (v5_relat_1(X3,X2)|~r1_tarski(X1,X2)|~v1_relat_1(X3)|~v5_relat_1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.19/0.42  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|esk3_0!=k1_xboole_0|~r1_tarski(k2_relat_1(esk6_0),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_96]), c_0_42]), c_0_64])])).
% 0.19/0.42  cnf(c_0_100, negated_conjecture, (k2_relat_1(esk6_0)=k1_xboole_0|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_94]), c_0_42])])).
% 0.19/0.42  cnf(c_0_101, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_84, c_0_97])).
% 0.19/0.42  cnf(c_0_102, negated_conjecture, (v5_relat_1(X1,esk5_0)|~v5_relat_1(X1,esk4_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_98, c_0_90])).
% 0.19/0.42  cnf(c_0_103, negated_conjecture, (v5_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_55, c_0_26])).
% 0.19/0.42  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|esk3_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_100]), c_0_64])])).
% 0.19/0.42  cnf(c_0_105, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|k1_relset_1(esk3_0,X1,esk6_0)!=esk3_0|~v5_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_81, c_0_97])).
% 0.19/0.42  cnf(c_0_106, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_103]), c_0_42])])).
% 0.19/0.42  cnf(c_0_107, negated_conjecture, (k1_relset_1(esk3_0,X1,esk6_0)=k1_relat_1(esk6_0)|~v5_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_97])).
% 0.19/0.42  cnf(c_0_108, negated_conjecture, (k1_relset_1(X1,X2,esk6_0)=k1_relat_1(esk6_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_25, c_0_104])).
% 0.19/0.42  cnf(c_0_109, negated_conjecture, (esk5_0=k1_xboole_0|k1_relset_1(esk3_0,esk5_0,esk6_0)!=esk3_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_102]), c_0_103]), c_0_42])]), c_0_106])).
% 0.19/0.42  cnf(c_0_110, negated_conjecture, (k1_relset_1(esk3_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_102]), c_0_103]), c_0_42])])).
% 0.19/0.42  cnf(c_0_111, negated_conjecture, (~v1_funct_2(esk6_0,esk3_0,esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_101, c_0_58])).
% 0.19/0.42  cnf(c_0_112, negated_conjecture, (X1=k1_xboole_0|v1_funct_2(esk6_0,esk3_0,X1)|k1_relat_1(esk6_0)!=esk3_0|esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_108]), c_0_96])).
% 0.19/0.42  cnf(c_0_113, negated_conjecture, (esk5_0=k1_xboole_0|k1_relat_1(esk6_0)!=esk3_0), inference(rw,[status(thm)],[c_0_109, c_0_110])).
% 0.19/0.42  cnf(c_0_114, negated_conjecture, (esk5_0=k1_xboole_0|k1_relat_1(esk6_0)!=esk3_0|esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_94])).
% 0.19/0.42  cnf(c_0_115, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_113, c_0_41])).
% 0.19/0.42  cnf(c_0_116, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_114, c_0_96])).
% 0.19/0.42  cnf(c_0_117, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_92])).
% 0.19/0.42  cnf(c_0_118, negated_conjecture, (esk3_0=k1_xboole_0|esk4_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_119, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_115]), c_0_66])).
% 0.19/0.42  cnf(c_0_120, negated_conjecture, (esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_116]), c_0_23]), c_0_94]), c_0_117])).
% 0.19/0.42  cnf(c_0_121, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_119])]), c_0_120]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 122
% 0.19/0.42  # Proof object clause steps            : 91
% 0.19/0.42  # Proof object formula steps           : 31
% 0.19/0.42  # Proof object conjectures             : 66
% 0.19/0.42  # Proof object clause conjectures      : 63
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 24
% 0.19/0.42  # Proof object initial formulas used   : 15
% 0.19/0.42  # Proof object generating inferences   : 62
% 0.19/0.42  # Proof object simplifying inferences  : 78
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 22
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 45
% 0.19/0.42  # Removed in clause preprocessing      : 1
% 0.19/0.42  # Initial clauses in saturation        : 44
% 0.19/0.42  # Processed clauses                    : 1141
% 0.19/0.42  # ...of these trivial                  : 7
% 0.19/0.42  # ...subsumed                          : 777
% 0.19/0.42  # ...remaining for further processing  : 357
% 0.19/0.42  # Other redundant clauses eliminated   : 51
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 112
% 0.19/0.42  # Backward-rewritten                   : 90
% 0.19/0.42  # Generated clauses                    : 1602
% 0.19/0.42  # ...of the previous two non-trivial   : 1231
% 0.19/0.42  # Contextual simplify-reflections      : 25
% 0.19/0.42  # Paramodulations                      : 1552
% 0.19/0.42  # Factorizations                       : 0
% 0.19/0.42  # Equation resolutions                 : 51
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
% 0.19/0.42  # Current number of processed clauses  : 146
% 0.19/0.42  #    Positive orientable unit clauses  : 24
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 2
% 0.19/0.42  #    Non-unit-clauses                  : 120
% 0.19/0.42  # Current number of unprocessed clauses: 65
% 0.19/0.42  # ...number of literals in the above   : 255
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 202
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 11925
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 6200
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 813
% 0.19/0.42  # Unit Clause-clause subsumption calls : 237
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 27
% 0.19/0.42  # BW rewrite match successes           : 10
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 25454
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.076 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.081 s
% 0.19/0.42  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
