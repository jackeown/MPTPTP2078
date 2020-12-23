%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1047+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:39 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  117 (23804 expanded)
%              Number of clauses        :   92 (9475 expanded)
%              Number of leaves         :   12 (5828 expanded)
%              Depth                    :   22
%              Number of atoms          :  463 (102759 expanded)
%              Number of equality atoms :  103 (14615 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal clause size      :   68 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t164_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_2)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t66_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,k1_tarski(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,k1_tarski(X2))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r2_relset_1(X1,k1_tarski(X2),X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(d7_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( X4 = k5_partfun1(X1,X2,X3)
        <=> ! [X5] :
              ( r2_hidden(X5,X4)
            <=> ? [X6] :
                  ( v1_funct_1(X6)
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & X6 = X5
                  & v1_partfun1(X6,X1)
                  & r1_partfun1(X3,X6) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

fof(t143_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
         => r1_partfun1(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_partfun1)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,k1_tarski(X2))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
           => k5_partfun1(X1,k1_tarski(X2),X3) = k1_tarski(X4) ) ) ),
    inference(assume_negation,[status(cth)],[t164_funct_2])).

fof(c_0_13,plain,(
    ! [X39,X40,X41,X42] :
      ( ( v1_funct_1(X42)
        | ~ r2_hidden(X42,k5_partfun1(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( v1_funct_2(X42,X39,X40)
        | ~ r2_hidden(X42,k5_partfun1(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ r2_hidden(X42,k5_partfun1(X39,X40,X41))
        | ~ v1_funct_1(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_14,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) != k1_tarski(esk9_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_15,plain,(
    ! [X43,X44] :
      ( ~ m1_subset_1(X43,X44)
      | v1_xboole_0(X44)
      | r2_hidden(X43,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,plain,(
    ! [X29] : m1_subset_1(esk5_1(X29),X29) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_17,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r2_relset_1(X31,X32,X33,X34)
        | X33 = X34
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X33 != X34
        | r2_relset_1(X31,X32,X33,X34)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk5_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X45,X46,X47] :
      ( ~ r2_hidden(X45,X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(X47))
      | ~ v1_xboole_0(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_24,plain,
    ( X3 = X4
    | ~ r2_relset_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    | ~ r2_hidden(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_28,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( X1 = esk9_0
    | ~ r2_relset_1(esk6_0,k1_tarski(esk7_0),X1,esk9_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    | v1_xboole_0(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_32,plain,(
    ! [X48,X49,X50,X51] :
      ( ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X48,k1_tarski(X49))
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,k1_tarski(X49))))
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,X48,k1_tarski(X49))
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X48,k1_tarski(X49))))
      | r2_relset_1(X48,k1_tarski(X49),X50,X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t66_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_19]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(X1,esk6_0,k1_tarski(esk7_0))
    | ~ r2_hidden(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_19]),c_0_20])])).

fof(c_0_35,plain,(
    ! [X52,X53] :
      ( ~ v1_xboole_0(X52)
      | X52 = X53
      | ~ v1_xboole_0(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,esk5_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( esk5_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = esk9_0
    | v1_xboole_0(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))
    | ~ r2_relset_1(esk6_0,k1_tarski(esk7_0),esk5_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,plain,
    ( r2_relset_1(X2,k1_tarski(X3),X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,k1_tarski(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,k1_tarski(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk5_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)))
    | v1_xboole_0(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk6_0,k1_tarski(esk7_0))
    | v1_xboole_0(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

fof(c_0_42,plain,(
    ! [X7,X8,X9] :
      ( ( v1_funct_1(X9)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | v1_xboole_0(X8) )
      & ( v1_partfun1(X9,X7)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | v1_xboole_0(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

cnf(c_0_43,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v1_xboole_0(esk5_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( esk5_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = esk9_0
    | v1_xboole_0(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_20]),c_0_19])]),c_0_31]),c_0_40]),c_0_41])).

cnf(c_0_46,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_47,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk1_2(X14,X15),X15)
        | esk1_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk1_2(X14,X15),X15)
        | esk1_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_48,plain,
    ( X1 = esk5_1(k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))
    | v1_xboole_0(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( v1_partfun1(esk9_0,esk6_0)
    | v1_xboole_0(k1_tarski(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_19]),c_0_39]),c_0_20])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = esk5_1(k1_zfmisc_1(X1))
    | r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_53,plain,(
    ! [X17,X18,X19,X20,X21,X23,X24,X25,X27] :
      ( ( v1_funct_1(esk2_5(X17,X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk2_5(X17,X18,X19,X20,X21),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( esk2_5(X17,X18,X19,X20,X21) = X21
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_partfun1(esk2_5(X17,X18,X19,X20,X21),X17)
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X19,esk2_5(X17,X18,X19,X20,X21))
        | ~ r2_hidden(X21,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ v1_funct_1(X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | X24 != X23
        | ~ v1_partfun1(X24,X17)
        | ~ r1_partfun1(X19,X24)
        | r2_hidden(X23,X20)
        | X20 != k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( ~ r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | ~ v1_funct_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | X27 != esk3_4(X17,X18,X19,X25)
        | ~ v1_partfun1(X27,X17)
        | ~ r1_partfun1(X19,X27)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_1(esk4_4(X17,X18,X19,X25))
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(esk4_4(X17,X18,X19,X25),k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( esk4_4(X17,X18,X19,X25) = esk3_4(X17,X18,X19,X25)
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_partfun1(esk4_4(X17,X18,X19,X25),X17)
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( r1_partfun1(X19,esk4_4(X17,X18,X19,X25))
        | r2_hidden(esk3_4(X17,X18,X19,X25),X25)
        | X25 = k5_partfun1(X17,X18,X19)
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_partfun1])])])])])])).

fof(c_0_54,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,k1_tarski(X36))))
      | ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,k1_tarski(X36))))
      | r1_partfun1(X37,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_partfun1])])])).

cnf(c_0_55,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(X1)) = k1_tarski(esk7_0)
    | v1_partfun1(esk9_0,esk6_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(X1)
    | m1_subset_1(esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))) = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)
    | r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_49])).

cnf(c_0_58,plain,
    ( r2_hidden(X4,X6)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X1 != X4
    | ~ v1_partfun1(X1,X2)
    | ~ r1_partfun1(X5,X1)
    | X6 != k5_partfun1(X2,X3,X5)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( r1_partfun1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3))))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k1_tarski(X3)))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( esk5_1(k1_zfmisc_1(k1_tarski(esk7_0))) = k1_tarski(esk7_0)
    | v1_partfun1(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_50])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = esk9_0
    | esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(X1)
    | ~ r2_relset_1(esk6_0,k1_tarski(esk7_0),esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))
    | ~ r2_hidden(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_57]),c_0_49])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_partfun1(X4,X1)
    | ~ v1_partfun1(X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( r1_partfun1(X1,esk9_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_19]),c_0_20])])).

cnf(c_0_66,negated_conjecture,
    ( v1_partfun1(esk9_0,esk6_0)
    | ~ r2_hidden(X1,k1_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_60]),c_0_50])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_61])])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk4_4(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(esk3_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_71,negated_conjecture,
    ( esk1_2(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = esk9_0
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(esk9_0)
    | ~ r2_relset_1(esk6_0,k1_tarski(esk7_0),esk1_2(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk9_0) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_62])])).

cnf(c_0_72,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(X1)
    | v1_funct_1(esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_51])).

cnf(c_0_73,negated_conjecture,
    ( esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = X1
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(X1)
    | v1_funct_2(esk1_2(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_51])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))
    | ~ r1_partfun1(esk9_0,X1)
    | ~ v1_partfun1(X1,esk6_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_20]),c_0_19])])).

cnf(c_0_75,negated_conjecture,
    ( r1_partfun1(esk9_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_19]),c_0_20])])).

cnf(c_0_76,negated_conjecture,
    ( v1_partfun1(esk9_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_77,negated_conjecture,
    ( X1 = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)
    | r2_hidden(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),X1)
    | m1_subset_1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])])).

cnf(c_0_78,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2)
    | esk1_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_79,negated_conjecture,
    ( esk1_2(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) = esk9_0
    | k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(esk9_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_38]),c_0_39]),c_0_20]),c_0_19])]),c_0_56]),c_0_72]),c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk9_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_19]),c_0_75]),c_0_76]),c_0_20])])).

cnf(c_0_81,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_82,plain,
    ( esk4_4(X1,X2,X3,X4) = esk3_4(X1,X2,X3,X4)
    | r2_hidden(esk3_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_83,plain,
    ( v1_funct_1(esk4_4(X1,X2,X3,X4))
    | r2_hidden(esk3_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_84,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)
    | m1_subset_1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    | m1_subset_1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0) = k1_tarski(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])])).

cnf(c_0_86,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) != k1_tarski(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_87,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1) = esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1)
    | X1 = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)
    | r2_hidden(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_69]),c_0_70])])).

cnf(c_0_89,negated_conjecture,
    ( X1 = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)
    | r2_hidden(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),X1)
    | v1_funct_1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_69]),c_0_70])])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    | m1_subset_1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_85]),c_0_85]),c_0_86])).

cnf(c_0_91,negated_conjecture,
    ( esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(X1)) = esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(X1))
    | esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(X1)) = X1
    | k1_tarski(X1) = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)
    | v1_funct_1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)))
    | v1_funct_1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_89])).

cnf(c_0_93,plain,
    ( v1_partfun1(esk4_4(X1,X2,X3,X4),X1)
    | r2_hidden(esk3_4(X1,X2,X3,X4),X4)
    | X4 = k5_partfun1(X1,X2,X3)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_94,plain,
    ( r1_partfun1(X1,esk4_4(X2,X3,X1,X4))
    | r2_hidden(esk3_4(X2,X3,X1,X4),X4)
    | X4 = k5_partfun1(X2,X3,X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_95,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | m1_subset_1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_86])).

cnf(c_0_96,negated_conjecture,
    ( v1_funct_1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)))
    | v1_funct_1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_85]),c_0_85]),c_0_85]),c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( X1 = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)
    | r2_hidden(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),X1)
    | v1_partfun1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_69]),c_0_70])])).

cnf(c_0_98,negated_conjecture,
    ( X1 = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)
    | r1_partfun1(esk8_0,esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1))
    | r2_hidden(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_69]),c_0_70])])).

cnf(c_0_99,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | ~ r2_relset_1(esk6_0,k1_tarski(esk7_0),esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | v1_funct_1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_91]),c_0_86])).

cnf(c_0_101,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)
    | v1_partfun1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk6_0)
    | v1_funct_2(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0) = k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)
    | r1_partfun1(esk8_0,esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)))
    | v1_funct_2(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk9_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | ~ v1_funct_2(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_38]),c_0_39]),c_0_20]),c_0_19])]),c_0_95]),c_0_100])).

cnf(c_0_104,negated_conjecture,
    ( v1_partfun1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk6_0)
    | v1_funct_2(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_101,c_0_85]),c_0_85]),c_0_85]),c_0_86])).

cnf(c_0_105,negated_conjecture,
    ( r1_partfun1(esk8_0,esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)))
    | v1_funct_2(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk6_0,k1_tarski(esk7_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_85]),c_0_85]),c_0_85]),c_0_86])).

cnf(c_0_106,negated_conjecture,
    ( v1_funct_2(X1,esk6_0,k1_tarski(esk7_0))
    | ~ r2_hidden(X1,k5_partfun1(esk6_0,k1_tarski(esk7_0),esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_69]),c_0_70])])).

cnf(c_0_107,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | v1_partfun1(esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_103,c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | r1_partfun1(esk8_0,esk4_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_103,c_0_105])).

cnf(c_0_109,plain,
    ( X4 = k5_partfun1(X1,X2,X3)
    | ~ r2_hidden(esk3_4(X1,X2,X3,X4),X4)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X5 != esk3_4(X1,X2,X3,X4)
    | ~ v1_partfun1(X5,X1)
    | ~ r1_partfun1(X3,X5)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_110,negated_conjecture,
    ( v1_funct_2(X1,esk6_0,k1_tarski(esk7_0))
    | ~ r1_partfun1(esk8_0,X1)
    | ~ v1_partfun1(X1,esk6_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_64]),c_0_70]),c_0_69])])).

cnf(c_0_111,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | v1_partfun1(esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_91]),c_0_86])).

cnf(c_0_112,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0
    | r1_partfun1(esk8_0,esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_91]),c_0_86])).

cnf(c_0_113,plain,
    ( X1 = k5_partfun1(X2,X3,X4)
    | ~ r1_partfun1(X4,esk3_4(X2,X3,X4,X1))
    | ~ r2_hidden(esk3_4(X2,X3,X4,X1),X1)
    | ~ v1_partfun1(esk3_4(X2,X3,X4,X1),X2)
    | ~ v1_funct_1(esk3_4(X2,X3,X4,X1))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(esk3_4(X2,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(er,[status(thm)],[c_0_109])).

cnf(c_0_114,negated_conjecture,
    ( esk3_4(esk6_0,k1_tarski(esk7_0),esk8_0,k1_tarski(esk9_0)) = esk9_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_110]),c_0_95]),c_0_100]),c_0_111]),c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( r1_partfun1(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_69]),c_0_70])])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_114]),c_0_115]),c_0_67]),c_0_76]),c_0_20]),c_0_70]),c_0_19]),c_0_69])]),c_0_86]),
    [proof]).

%------------------------------------------------------------------------------
