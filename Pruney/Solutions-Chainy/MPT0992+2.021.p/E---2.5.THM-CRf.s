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
% DateTime   : Thu Dec  3 11:03:37 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  121 (4927 expanded)
%              Number of clauses        :   84 (1971 expanded)
%              Number of leaves         :   19 (1222 expanded)
%              Depth                    :   17
%              Number of atoms          :  331 (23405 expanded)
%              Number of equality atoms :   95 (5218 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(fc8_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k7_relat_1(X1,X2))
        & v1_funct_1(k7_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(t110_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

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

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc3_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X3,X1)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
              & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
              & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_2])).

fof(c_0_20,plain,(
    ! [X21,X22] :
      ( ( v1_relat_1(k7_relat_1(X21,X22))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) )
      & ( v1_funct_1(k7_relat_1(X21,X22))
        | ~ v1_relat_1(X21)
        | ~ v1_funct_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).

fof(c_0_21,plain,(
    ! [X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,k1_xboole_0) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).

fof(c_0_22,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | v1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk3_0,esk1_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
      | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
      | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

cnf(c_0_24,plain,
    ( v1_funct_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X32,X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_relset_1(X32,X33,X34) = k1_relat_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_29,plain,(
    ! [X38,X39,X40,X41] :
      ( ( v1_funct_1(k2_partfun1(X38,X39,X40,X41))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | ~ v1_funct_1(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_30,plain,(
    ! [X42,X43,X44,X45] :
      ( ~ v1_funct_1(X44)
      | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | k2_partfun1(X42,X43,X44,X45) = k7_relat_1(X44,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_31,plain,(
    ! [X10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_32,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_36,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X36 = k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X35 = k1_relset_1(X35,X36,X37)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X35 != k1_relset_1(X35,X36,X37)
        | v1_funct_2(X37,X35,X36)
        | X35 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( ~ v1_funct_2(X37,X35,X36)
        | X37 = k1_xboole_0
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( X37 != k1_xboole_0
        | v1_funct_2(X37,X35,X36)
        | X35 = k1_xboole_0
        | X36 != k1_xboole_0
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_37,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_38,plain,(
    ! [X26,X27,X28] :
      ( ( v4_relat_1(X28,X26)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v5_relat_1(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])])).

fof(c_0_43,plain,(
    ! [X46,X47] :
      ( ( v1_funct_1(X47)
        | ~ r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( v1_funct_2(X47,k1_relat_1(X47),X46)
        | ~ r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X47),X46)))
        | ~ r1_tarski(k2_relat_1(X47),X46)
        | ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_45,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(X17,k1_relat_1(X18))
      | k1_relat_1(k7_relat_1(X18,X17)) = X17 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_46,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_27])).

fof(c_0_49,plain,(
    ! [X14,X15] :
      ( ( ~ v5_relat_1(X15,X14)
        | r1_tarski(k2_relat_1(X15),X14)
        | ~ v1_relat_1(X15) )
      & ( ~ r1_tarski(k2_relat_1(X15),X14)
        | v5_relat_1(X15,X14)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_50,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_27]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(esk1_0,esk2_0,esk4_0,X1) = k7_relat_1(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_27]),c_0_34])])).

fof(c_0_53,plain,(
    ! [X29,X30,X31] :
      ( ~ v1_xboole_0(X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_xboole_0(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).

cnf(c_0_54,plain,
    ( k2_partfun1(X1,X2,k1_xboole_0,X3) = k7_relat_1(k1_xboole_0,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_57,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_27])])).

cnf(c_0_59,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_60,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_41])).

cnf(c_0_61,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_62,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_41])).

cnf(c_0_63,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(k2_partfun1(esk1_0,esk2_0,esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_51])).

fof(c_0_66,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( m1_subset_1(k7_relat_1(k1_xboole_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_41]),c_0_42])]),c_0_54])).

cnf(c_0_69,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,X1)) = X1
    | esk2_0 = k1_xboole_0
    | ~ r1_tarski(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_33])])).

cnf(c_0_71,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_34])])).

cnf(c_0_73,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_64])).

cnf(c_0_74,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_65,c_0_52])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_76,plain,
    ( v1_xboole_0(k7_relat_1(k1_xboole_0,X1))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,k1_xboole_0)) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k7_relat_1(esk4_0,X1)) ),
    inference(rw,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_80,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))
    | ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_82,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_73]),c_0_74])])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_85,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_86,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(k7_relat_1(esk4_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_74]),c_0_80])])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_72])])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(k7_relat_1(esk4_0,X1),k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_79]),c_0_74])])).

cnf(c_0_89,negated_conjecture,
    ( k1_relat_1(k7_relat_1(esk4_0,esk3_0)) = esk3_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_70,c_0_84])).

fof(c_0_90,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | X8 = X9
      | ~ v1_xboole_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_91,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_92,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_52]),c_0_52])).

cnf(c_0_95,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_96,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( esk3_0 = esk1_0
    | ~ r1_tarski(esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_91,c_0_84])).

cnf(c_0_98,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_99,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_100,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_83]),c_0_79]),c_0_74])])).

cnf(c_0_102,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_103,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3)
    | ~ v1_xboole_0(k1_relat_1(X1))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_57,c_0_96])).

cnf(c_0_104,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_71])])).

cnf(c_0_105,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_99])).

cnf(c_0_106,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_41]),c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_96])]),c_0_80])])).

cnf(c_0_108,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_89]),c_0_102])).

cnf(c_0_109,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X1)) = X1
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_100]),c_0_62]),c_0_80])])).

cnf(c_0_110,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0
    | ~ v1_funct_2(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_94,c_0_104])).

cnf(c_0_111,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_41])])).

cnf(c_0_112,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_113,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_108]),c_0_80])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,esk3_0)) = esk3_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_109,c_0_84])).

cnf(c_0_115,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_25]),c_0_111]),c_0_41]),c_0_33])])).

cnf(c_0_116,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112,c_0_113]),c_0_80])])).

cnf(c_0_117,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_xboole_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115]),c_0_100])).

cnf(c_0_118,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_113]),c_0_80])])).

cnf(c_0_120,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_108]),c_0_108]),c_0_118]),c_0_119]),c_0_115]),c_0_119]),c_0_111]),c_0_118]),c_0_119]),c_0_115]),c_0_119]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.50  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.041 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 0.19/0.50  fof(fc8_funct_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k7_relat_1(X1,X2))&v1_funct_1(k7_relat_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 0.19/0.50  fof(t110_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 0.19/0.50  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.50  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.50  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.19/0.50  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.50  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.50  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 0.19/0.50  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 0.19/0.50  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.50  fof(cc3_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 0.19/0.50  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.50  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.50  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.19/0.50  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 0.19/0.50  fof(c_0_20, plain, ![X21, X22]:((v1_relat_1(k7_relat_1(X21,X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))&(v1_funct_1(k7_relat_1(X21,X22))|(~v1_relat_1(X21)|~v1_funct_1(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc8_funct_1])])])).
% 0.19/0.50  fof(c_0_21, plain, ![X16]:(~v1_relat_1(X16)|k7_relat_1(X16,k1_xboole_0)=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t110_relat_1])])).
% 0.19/0.50  fof(c_0_22, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|v1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.50  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk3_0,esk1_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.19/0.50  cnf(c_0_24, plain, (v1_funct_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_25, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  fof(c_0_28, plain, ![X32, X33, X34]:(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k1_relset_1(X32,X33,X34)=k1_relat_1(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.50  fof(c_0_29, plain, ![X38, X39, X40, X41]:((v1_funct_1(k2_partfun1(X38,X39,X40,X41))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&(m1_subset_1(k2_partfun1(X38,X39,X40,X41),k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.19/0.50  fof(c_0_30, plain, ![X42, X43, X44, X45]:(~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|k2_partfun1(X42,X43,X44,X45)=k7_relat_1(X44,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.50  fof(c_0_31, plain, ![X10]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.50  cnf(c_0_32, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.50  cnf(c_0_33, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.50  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  fof(c_0_35, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  fof(c_0_36, plain, ![X35, X36, X37]:((((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X36=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&((~v1_funct_2(X37,X35,X36)|X35=k1_relset_1(X35,X36,X37)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X35!=k1_relset_1(X35,X36,X37)|v1_funct_2(X37,X35,X36)|X35!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&((~v1_funct_2(X37,X35,X36)|X37=k1_xboole_0|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(X37!=k1_xboole_0|v1_funct_2(X37,X35,X36)|X35=k1_xboole_0|X36!=k1_xboole_0|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.50  cnf(c_0_37, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.50  fof(c_0_38, plain, ![X26, X27, X28]:((v4_relat_1(X28,X26)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(v5_relat_1(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.50  cnf(c_0_39, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.50  cnf(c_0_40, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.50  cnf(c_0_41, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])])).
% 0.19/0.50  fof(c_0_43, plain, ![X46, X47]:(((v1_funct_1(X47)|~r1_tarski(k2_relat_1(X47),X46)|(~v1_relat_1(X47)|~v1_funct_1(X47)))&(v1_funct_2(X47,k1_relat_1(X47),X46)|~r1_tarski(k2_relat_1(X47),X46)|(~v1_relat_1(X47)|~v1_funct_1(X47))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X47),X46)))|~r1_tarski(k2_relat_1(X47),X46)|(~v1_relat_1(X47)|~v1_funct_1(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.19/0.50  cnf(c_0_44, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  fof(c_0_45, plain, ![X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(X17,k1_relat_1(X18))|k1_relat_1(k7_relat_1(X18,X17))=X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 0.19/0.50  cnf(c_0_46, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.50  cnf(c_0_47, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  cnf(c_0_48, negated_conjecture, (k1_relset_1(esk1_0,esk2_0,esk4_0)=k1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_37, c_0_27])).
% 0.19/0.50  fof(c_0_49, plain, ![X14, X15]:((~v5_relat_1(X15,X14)|r1_tarski(k2_relat_1(X15),X14)|~v1_relat_1(X15))&(~r1_tarski(k2_relat_1(X15),X14)|v5_relat_1(X15,X14)|~v1_relat_1(X15))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.50  cnf(c_0_50, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.50  cnf(c_0_51, negated_conjecture, (m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_27]), c_0_34])])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (k2_partfun1(esk1_0,esk2_0,esk4_0,X1)=k7_relat_1(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_27]), c_0_34])])).
% 0.19/0.50  fof(c_0_53, plain, ![X29, X30, X31]:(~v1_xboole_0(X29)|(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_relset_1])])])).
% 0.19/0.50  cnf(c_0_54, plain, (k2_partfun1(X1,X2,k1_xboole_0,X3)=k7_relat_1(k1_xboole_0,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.19/0.50  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.50  cnf(c_0_56, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_44])).
% 0.19/0.50  cnf(c_0_57, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_27])])).
% 0.19/0.50  cnf(c_0_59, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.50  cnf(c_0_60, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_50, c_0_41])).
% 0.19/0.50  cnf(c_0_61, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.50  cnf(c_0_62, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_26, c_0_41])).
% 0.19/0.50  cnf(c_0_63, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (v1_relat_1(k2_partfun1(esk1_0,esk2_0,esk4_0,X1))), inference(spm,[status(thm)],[c_0_26, c_0_51])).
% 0.19/0.50  fof(c_0_66, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.50  cnf(c_0_67, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.50  cnf(c_0_68, plain, (m1_subset_1(k7_relat_1(k1_xboole_0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_41]), c_0_42])]), c_0_54])).
% 0.19/0.50  cnf(c_0_69, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,X1))=X1|esk2_0=k1_xboole_0|~r1_tarski(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_33])])).
% 0.19/0.50  cnf(c_0_71, plain, (r1_tarski(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_27]), c_0_34])])).
% 0.19/0.50  cnf(c_0_73, negated_conjecture, (v5_relat_1(k7_relat_1(esk4_0,X1),esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_64])).
% 0.19/0.50  cnf(c_0_74, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[c_0_65, c_0_52])).
% 0.19/0.50  cnf(c_0_75, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.50  cnf(c_0_76, plain, (v1_xboole_0(k7_relat_1(k1_xboole_0,X1))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.19/0.50  cnf(c_0_77, plain, (v1_xboole_0(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_67, c_0_69])).
% 0.19/0.50  cnf(c_0_78, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,k1_xboole_0))=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.50  cnf(c_0_79, negated_conjecture, (v1_funct_1(k7_relat_1(esk4_0,X1))), inference(rw,[status(thm)],[c_0_72, c_0_52])).
% 0.19/0.50  cnf(c_0_80, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.50  cnf(c_0_81, negated_conjecture, (~v1_funct_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0))|~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  cnf(c_0_82, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.50  cnf(c_0_83, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_73]), c_0_74])])).
% 0.19/0.50  cnf(c_0_84, negated_conjecture, (r1_tarski(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  cnf(c_0_85, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.50  cnf(c_0_86, negated_conjecture, (esk2_0=k1_xboole_0|v1_xboole_0(k7_relat_1(esk4_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_74]), c_0_80])])).
% 0.19/0.50  cnf(c_0_87, negated_conjecture, (~v1_funct_2(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k2_partfun1(esk1_0,esk2_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_72])])).
% 0.19/0.50  cnf(c_0_88, negated_conjecture, (v1_funct_2(k7_relat_1(esk4_0,X1),k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_79]), c_0_74])])).
% 0.19/0.50  cnf(c_0_89, negated_conjecture, (k1_relat_1(k7_relat_1(esk4_0,esk3_0))=esk3_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_70, c_0_84])).
% 0.19/0.50  fof(c_0_90, plain, ![X8, X9]:(~v1_xboole_0(X8)|X8=X9|~v1_xboole_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.19/0.50  cnf(c_0_91, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_92, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.50  cnf(c_0_93, negated_conjecture, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.19/0.50  cnf(c_0_94, negated_conjecture, (~v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_52]), c_0_52])).
% 0.19/0.50  cnf(c_0_95, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(k7_relat_1(esk4_0,esk3_0),esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.19/0.50  cnf(c_0_96, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.19/0.50  cnf(c_0_97, negated_conjecture, (esk3_0=esk1_0|~r1_tarski(esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_91, c_0_84])).
% 0.19/0.50  cnf(c_0_98, negated_conjecture, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 0.19/0.50  cnf(c_0_99, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.50  cnf(c_0_100, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.50  cnf(c_0_101, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(esk4_0,X1)),esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_83]), c_0_79]), c_0_74])])).
% 0.19/0.50  cnf(c_0_102, negated_conjecture, (esk2_0=k1_xboole_0|~m1_subset_1(k7_relat_1(esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.50  cnf(c_0_103, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,X3)|~v1_xboole_0(k1_relat_1(X1))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_57, c_0_96])).
% 0.19/0.50  cnf(c_0_104, negated_conjecture, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_71])])).
% 0.19/0.50  cnf(c_0_105, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_99])).
% 0.19/0.50  cnf(c_0_106, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_41]), c_0_100])).
% 0.19/0.50  cnf(c_0_107, negated_conjecture, (esk1_0=k1_xboole_0|~v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_96])]), c_0_80])])).
% 0.19/0.50  cnf(c_0_108, negated_conjecture, (esk2_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_89]), c_0_102])).
% 0.19/0.50  cnf(c_0_109, plain, (k1_relat_1(k7_relat_1(k1_xboole_0,X1))=X1|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_100]), c_0_62]), c_0_80])])).
% 0.19/0.50  cnf(c_0_110, negated_conjecture, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0|~v1_funct_2(k7_relat_1(esk4_0,k1_xboole_0),k1_xboole_0,esk2_0)|~m1_subset_1(k7_relat_1(esk4_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_94, c_0_104])).
% 0.19/0.50  cnf(c_0_111, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_41])])).
% 0.19/0.50  cnf(c_0_112, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_67, c_0_27])).
% 0.19/0.50  cnf(c_0_113, negated_conjecture, (esk1_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_108]), c_0_80])])).
% 0.19/0.50  cnf(c_0_114, negated_conjecture, (k1_relat_1(k7_relat_1(k1_xboole_0,esk3_0))=esk3_0|~v1_xboole_0(esk1_0)), inference(spm,[status(thm)],[c_0_109, c_0_84])).
% 0.19/0.50  cnf(c_0_115, negated_conjecture, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_25]), c_0_111]), c_0_41]), c_0_33])])).
% 0.19/0.50  cnf(c_0_116, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_112, c_0_113]), c_0_80])])).
% 0.19/0.50  cnf(c_0_117, negated_conjecture, (esk3_0=k1_xboole_0|~v1_xboole_0(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115]), c_0_100])).
% 0.19/0.50  cnf(c_0_118, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_116])).
% 0.19/0.50  cnf(c_0_119, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_113]), c_0_80])])).
% 0.19/0.50  cnf(c_0_120, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_108]), c_0_108]), c_0_118]), c_0_119]), c_0_115]), c_0_119]), c_0_111]), c_0_118]), c_0_119]), c_0_115]), c_0_119]), c_0_41])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 121
% 0.19/0.50  # Proof object clause steps            : 84
% 0.19/0.50  # Proof object formula steps           : 37
% 0.19/0.50  # Proof object conjectures             : 48
% 0.19/0.50  # Proof object clause conjectures      : 45
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 29
% 0.19/0.50  # Proof object initial formulas used   : 19
% 0.19/0.50  # Proof object generating inferences   : 43
% 0.19/0.50  # Proof object simplifying inferences  : 82
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 21
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 40
% 0.19/0.50  # Removed in clause preprocessing      : 1
% 0.19/0.50  # Initial clauses in saturation        : 39
% 0.19/0.50  # Processed clauses                    : 1269
% 0.19/0.50  # ...of these trivial                  : 24
% 0.19/0.50  # ...subsumed                          : 681
% 0.19/0.50  # ...remaining for further processing  : 563
% 0.19/0.50  # Other redundant clauses eliminated   : 46
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 87
% 0.19/0.50  # Backward-rewritten                   : 321
% 0.19/0.50  # Generated clauses                    : 5050
% 0.19/0.50  # ...of the previous two non-trivial   : 4596
% 0.19/0.50  # Contextual simplify-reflections      : 16
% 0.19/0.50  # Paramodulations                      : 5005
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 46
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 111
% 0.19/0.50  #    Positive orientable unit clauses  : 18
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 0
% 0.19/0.50  #    Non-unit-clauses                  : 93
% 0.19/0.50  # Current number of unprocessed clauses: 3218
% 0.19/0.50  # ...number of literals in the above   : 12976
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 446
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 19786
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 11804
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 768
% 0.19/0.50  # Unit Clause-clause subsumption calls : 542
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 100
% 0.19/0.50  # BW rewrite match successes           : 32
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 65194
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.154 s
% 0.19/0.50  # System time              : 0.008 s
% 0.19/0.50  # Total time               : 0.162 s
% 0.19/0.50  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
