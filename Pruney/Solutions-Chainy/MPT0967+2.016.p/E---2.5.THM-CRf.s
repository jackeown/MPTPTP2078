%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:23 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 499 expanded)
%              Number of clauses        :   57 ( 225 expanded)
%              Number of leaves         :    9 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  247 (2278 expanded)
%              Number of equality atoms :   75 ( 567 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(t8_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X10] : r1_tarski(k1_xboole_0,X10) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(esk2_0,esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_12,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(X7,X8)
      | ~ r1_tarski(X8,X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_13,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

fof(c_0_15,plain,(
    ! [X30,X31,X32,X33] :
      ( ( v1_funct_1(X33)
        | X31 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X30,X31,X33),X32)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_2(X33,X30,X32)
        | X31 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X30,X31,X33),X32)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))
        | X31 = k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X30,X31,X33),X32)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_1(X33)
        | X30 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X30,X31,X33),X32)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v1_funct_2(X33,X30,X32)
        | X30 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X30,X31,X33),X32)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))
        | X30 != k1_xboole_0
        | ~ r1_tarski(k2_relset_1(X30,X31,X33),X32)
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X30,X31)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | m1_subset_1(k2_relset_1(X25,X26,X27),k1_zfmisc_1(X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_18,plain,(
    ! [X11,X12] :
      ( ( k2_zfmisc_1(X11,X12) != k1_xboole_0
        | X11 = k1_xboole_0
        | X12 = k1_xboole_0 )
      & ( X11 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X11,X12) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( r1_tarski(o_0_0_xboole_0,X1) ),
    inference(rw,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_23,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19,c_0_20])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,o_0_0_xboole_0) ),
    inference(pm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( X1 = o_0_0_xboole_0
    | v1_funct_2(X2,X3,X4)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),X4) ),
    inference(rw,[status(thm)],[c_0_24,c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,plain,
    ( r1_tarski(k2_relset_1(X1,X2,X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk2_0)) ),
    inference(pm,[status(thm)],[c_0_25,c_0_27])).

cnf(c_0_38,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | X2 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_14]),c_0_14])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(pm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | X1 != o_0_0_xboole_0 ),
    inference(pm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | v1_funct_2(esk4_0,esk1_0,X1)
    | ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33,c_0_27]),c_0_34]),c_0_20])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ r1_tarski(X1,esk2_0) ),
    inference(pm,[status(thm)],[c_0_21,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk2_0) ),
    inference(pm,[status(thm)],[c_0_36,c_0_27])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk4_0,o_0_0_xboole_0)
    | esk2_0 != o_0_0_xboole_0 ),
    inference(pm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,X2) = o_0_0_xboole_0
    | X1 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_14]),c_0_14])).

cnf(c_0_48,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != o_0_0_xboole_0
    | ~ v1_funct_2(X1,X2,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3) ),
    inference(rw,[status(thm)],[c_0_40,c_0_14])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 != o_0_0_xboole_0
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(pm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_0,X1)
    | esk2_0 != o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21,c_0_46]),c_0_22])])).

cnf(c_0_54,negated_conjecture,
    ( o_0_0_xboole_0 != esk1_0
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(pm,[status(thm)],[c_0_29,c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0))
    | o_0_0_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,X1)
    | o_0_0_xboole_0 != esk1_0
    | ~ r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_27]),c_0_34]),c_0_20])])).

cnf(c_0_57,negated_conjecture,
    ( o_0_0_xboole_0 = esk1_0
    | esk2_0 != o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_14]),c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 = o_0_0_xboole_0
    | esk4_0 != o_0_0_xboole_0 ),
    inference(pm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( esk4_0 = X1
    | esk2_0 != o_0_0_xboole_0
    | ~ r1_tarski(X1,esk4_0) ),
    inference(pm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( o_0_0_xboole_0 != esk1_0
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(pm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | o_0_0_xboole_0 != esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56,c_0_44]),c_0_45])])).

cnf(c_0_62,negated_conjecture,
    ( o_0_0_xboole_0 = esk1_0
    | esk4_0 != o_0_0_xboole_0 ),
    inference(pm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( esk4_0 = X1
    | esk2_0 != o_0_0_xboole_0
    | X1 != o_0_0_xboole_0 ),
    inference(pm,[status(thm)],[c_0_59,c_0_42])).

cnf(c_0_64,negated_conjecture,
    ( o_0_0_xboole_0 != esk1_0 ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0
    | X1 != o_0_0_xboole_0 ),
    inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X2,X4,X1),X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 != o_0_0_xboole_0 ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_68,plain,
    ( X1 = o_0_0_xboole_0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),X4) ),
    inference(rw,[status(thm)],[c_0_66,c_0_14])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_51,c_0_67])).

cnf(c_0_70,plain,
    ( X1 = o_0_0_xboole_0
    | r1_tarski(X2,k2_zfmisc_1(X3,X4))
    | ~ v1_funct_2(X2,X3,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),X4) ),
    inference(pm,[status(thm)],[c_0_25,c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(pm,[status(thm)],[c_0_21,c_0_45])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,X1))
    | ~ r1_tarski(esk2_0,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_71]),c_0_34]),c_0_20]),c_0_27])]),c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72,c_0_73]),c_0_35])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:20:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.50  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.18/0.50  # and selection function NoSelection.
% 0.18/0.50  #
% 0.18/0.50  # Preprocessing time       : 0.016 s
% 0.18/0.50  
% 0.18/0.50  # Proof found!
% 0.18/0.50  # SZS status Theorem
% 0.18/0.50  # SZS output start CNFRefutation
% 0.18/0.50  fof(t9_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 0.18/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.18/0.50  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.50  fof(d2_xboole_0, axiom, k1_xboole_0=o_0_0_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 0.18/0.50  fof(t8_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 0.18/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.18/0.50  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.18/0.50  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.18/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.18/0.50  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t9_funct_2])).
% 0.18/0.50  fof(c_0_10, plain, ![X10]:r1_tarski(k1_xboole_0,X10), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.18/0.50  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(esk2_0,esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.18/0.50  fof(c_0_12, plain, ![X7, X8, X9]:(~r1_tarski(X7,X8)|~r1_tarski(X8,X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.50  cnf(c_0_13, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.50  cnf(c_0_14, plain, (k1_xboole_0=o_0_0_xboole_0), inference(split_conjunct,[status(thm)],[d2_xboole_0])).
% 0.18/0.50  fof(c_0_15, plain, ![X30, X31, X32, X33]:((((v1_funct_1(X33)|X31=k1_xboole_0|~r1_tarski(k2_relset_1(X30,X31,X33),X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(v1_funct_2(X33,X30,X32)|X31=k1_xboole_0|~r1_tarski(k2_relset_1(X30,X31,X33),X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))|X31=k1_xboole_0|~r1_tarski(k2_relset_1(X30,X31,X33),X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(((v1_funct_1(X33)|X30!=k1_xboole_0|~r1_tarski(k2_relset_1(X30,X31,X33),X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(v1_funct_2(X33,X30,X32)|X30!=k1_xboole_0|~r1_tarski(k2_relset_1(X30,X31,X33),X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))&(m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X32)))|X30!=k1_xboole_0|~r1_tarski(k2_relset_1(X30,X31,X33),X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,X30,X31)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_2])])])).
% 0.18/0.50  fof(c_0_16, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.18/0.50  fof(c_0_17, plain, ![X25, X26, X27]:(~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|m1_subset_1(k2_relset_1(X25,X26,X27),k1_zfmisc_1(X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.18/0.50  fof(c_0_18, plain, ![X11, X12]:((k2_zfmisc_1(X11,X12)!=k1_xboole_0|(X11=k1_xboole_0|X12=k1_xboole_0))&((X11!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0)&(X12!=k1_xboole_0|k2_zfmisc_1(X11,X12)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.18/0.50  cnf(c_0_19, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_21, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.50  cnf(c_0_22, plain, (r1_tarski(o_0_0_xboole_0,X1)), inference(rw,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.50  fof(c_0_23, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.18/0.50  cnf(c_0_24, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.50  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.50  cnf(c_0_26, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.50  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_28, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.50  cnf(c_0_29, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_19, c_0_20])])).
% 0.18/0.50  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.50  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,o_0_0_xboole_0)), inference(pm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.50  cnf(c_0_32, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.50  cnf(c_0_33, plain, (X1=o_0_0_xboole_0|v1_funct_2(X2,X3,X4)|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(k2_relset_1(X3,X1,X2),X4)), inference(rw,[status(thm)],[c_0_24, c_0_14])).
% 0.18/0.50  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_35, negated_conjecture, (r1_tarski(esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_36, plain, (r1_tarski(k2_relset_1(X1,X2,X3),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.50  cnf(c_0_37, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk2_0))), inference(pm,[status(thm)],[c_0_25, c_0_27])).
% 0.18/0.50  cnf(c_0_38, plain, (k2_zfmisc_1(X1,X2)=o_0_0_xboole_0|X2!=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_14]), c_0_14])).
% 0.18/0.50  cnf(c_0_39, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.50  cnf(c_0_40, plain, (v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.50  cnf(c_0_41, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))), inference(pm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.50  cnf(c_0_42, plain, (r1_tarski(X1,X2)|X1!=o_0_0_xboole_0), inference(pm,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.50  cnf(c_0_43, negated_conjecture, (esk2_0=o_0_0_xboole_0|v1_funct_2(esk4_0,esk1_0,X1)|~r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_33, c_0_27]), c_0_34]), c_0_20])])).
% 0.18/0.50  cnf(c_0_44, negated_conjecture, (r1_tarski(X1,esk3_0)|~r1_tarski(X1,esk2_0)), inference(pm,[status(thm)],[c_0_21, c_0_35])).
% 0.18/0.50  cnf(c_0_45, negated_conjecture, (r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk2_0)), inference(pm,[status(thm)],[c_0_36, c_0_27])).
% 0.18/0.50  cnf(c_0_46, negated_conjecture, (r1_tarski(esk4_0,o_0_0_xboole_0)|esk2_0!=o_0_0_xboole_0), inference(pm,[status(thm)],[c_0_37, c_0_38])).
% 0.18/0.50  cnf(c_0_47, plain, (k2_zfmisc_1(X1,X2)=o_0_0_xboole_0|X1!=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_14]), c_0_14])).
% 0.18/0.50  cnf(c_0_48, plain, (v1_funct_2(X1,X2,X3)|X2!=o_0_0_xboole_0|~v1_funct_2(X1,X2,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~r1_tarski(k2_relset_1(X2,X4,X1),X3)), inference(rw,[status(thm)],[c_0_40, c_0_14])).
% 0.18/0.50  cnf(c_0_49, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.18/0.50  cnf(c_0_50, negated_conjecture, (esk4_0!=o_0_0_xboole_0|~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(pm,[status(thm)],[c_0_41, c_0_42])).
% 0.18/0.50  cnf(c_0_51, negated_conjecture, (esk2_0=o_0_0_xboole_0|v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.18/0.50  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.18/0.50  cnf(c_0_53, negated_conjecture, (r1_tarski(esk4_0,X1)|esk2_0!=o_0_0_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_21, c_0_46]), c_0_22])])).
% 0.18/0.50  cnf(c_0_54, negated_conjecture, (o_0_0_xboole_0!=esk1_0|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0))), inference(pm,[status(thm)],[c_0_29, c_0_47])).
% 0.18/0.50  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(o_0_0_xboole_0))|o_0_0_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_27, c_0_47])).
% 0.18/0.50  cnf(c_0_56, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,X1)|o_0_0_xboole_0!=esk1_0|~r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_27]), c_0_34]), c_0_20])])).
% 0.18/0.50  cnf(c_0_57, negated_conjecture, (o_0_0_xboole_0=esk1_0|esk2_0!=o_0_0_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_14]), c_0_14])).
% 0.18/0.50  cnf(c_0_58, negated_conjecture, (esk2_0=o_0_0_xboole_0|esk4_0!=o_0_0_xboole_0), inference(pm,[status(thm)],[c_0_50, c_0_51])).
% 0.18/0.50  cnf(c_0_59, negated_conjecture, (esk4_0=X1|esk2_0!=o_0_0_xboole_0|~r1_tarski(X1,esk4_0)), inference(pm,[status(thm)],[c_0_52, c_0_53])).
% 0.18/0.50  cnf(c_0_60, negated_conjecture, (o_0_0_xboole_0!=esk1_0|~v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(pm,[status(thm)],[c_0_54, c_0_55])).
% 0.18/0.50  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|o_0_0_xboole_0!=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_56, c_0_44]), c_0_45])])).
% 0.18/0.50  cnf(c_0_62, negated_conjecture, (o_0_0_xboole_0=esk1_0|esk4_0!=o_0_0_xboole_0), inference(pm,[status(thm)],[c_0_57, c_0_58])).
% 0.18/0.50  cnf(c_0_63, negated_conjecture, (esk4_0=X1|esk2_0!=o_0_0_xboole_0|X1!=o_0_0_xboole_0), inference(pm,[status(thm)],[c_0_59, c_0_42])).
% 0.18/0.50  cnf(c_0_64, negated_conjecture, (o_0_0_xboole_0!=esk1_0), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.18/0.50  cnf(c_0_65, negated_conjecture, (esk2_0!=o_0_0_xboole_0|X1!=o_0_0_xboole_0), inference(sr,[status(thm)],[inference(pm,[status(thm)],[c_0_62, c_0_63]), c_0_64])).
% 0.18/0.50  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(k2_relset_1(X2,X4,X1),X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.50  cnf(c_0_67, negated_conjecture, (esk2_0!=o_0_0_xboole_0), inference(er,[status(thm)],[c_0_65])).
% 0.18/0.50  cnf(c_0_68, plain, (X1=o_0_0_xboole_0|m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(k2_relset_1(X3,X1,X2),X4)), inference(rw,[status(thm)],[c_0_66, c_0_14])).
% 0.18/0.50  cnf(c_0_69, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(sr,[status(thm)],[c_0_51, c_0_67])).
% 0.18/0.50  cnf(c_0_70, plain, (X1=o_0_0_xboole_0|r1_tarski(X2,k2_zfmisc_1(X3,X4))|~v1_funct_2(X2,X3,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(k2_relset_1(X3,X1,X2),X4)), inference(pm,[status(thm)],[c_0_25, c_0_68])).
% 0.18/0.50  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),X1)|~r1_tarski(esk2_0,X1)), inference(pm,[status(thm)],[c_0_21, c_0_45])).
% 0.18/0.50  cnf(c_0_72, negated_conjecture, (~r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_69])])).
% 0.18/0.50  cnf(c_0_73, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk1_0,X1))|~r1_tarski(esk2_0,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_71]), c_0_34]), c_0_20]), c_0_27])]), c_0_67])).
% 0.18/0.50  cnf(c_0_74, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_72, c_0_73]), c_0_35])]), ['proof']).
% 0.18/0.50  # SZS output end CNFRefutation
% 0.18/0.50  # Proof object total steps             : 75
% 0.18/0.50  # Proof object clause steps            : 57
% 0.18/0.50  # Proof object formula steps           : 18
% 0.18/0.50  # Proof object conjectures             : 37
% 0.18/0.50  # Proof object clause conjectures      : 34
% 0.18/0.50  # Proof object formula conjectures     : 3
% 0.18/0.50  # Proof object initial clauses used    : 19
% 0.18/0.50  # Proof object initial formulas used   : 9
% 0.18/0.50  # Proof object generating inferences   : 28
% 0.18/0.50  # Proof object simplifying inferences  : 35
% 0.18/0.50  # Training examples: 0 positive, 0 negative
% 0.18/0.50  # Parsed axioms                        : 16
% 0.18/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.50  # Initial clauses                      : 36
% 0.18/0.50  # Removed in clause preprocessing      : 4
% 0.18/0.50  # Initial clauses in saturation        : 32
% 0.18/0.50  # Processed clauses                    : 2810
% 0.18/0.50  # ...of these trivial                  : 45
% 0.18/0.50  # ...subsumed                          : 2039
% 0.18/0.50  # ...remaining for further processing  : 726
% 0.18/0.50  # Other redundant clauses eliminated   : 0
% 0.18/0.50  # Clauses deleted for lack of memory   : 0
% 0.18/0.50  # Backward-subsumed                    : 96
% 0.18/0.50  # Backward-rewritten                   : 72
% 0.18/0.50  # Generated clauses                    : 17850
% 0.18/0.50  # ...of the previous two non-trivial   : 15748
% 0.18/0.50  # Contextual simplify-reflections      : 0
% 0.18/0.50  # Paramodulations                      : 17812
% 0.18/0.50  # Factorizations                       : 0
% 0.18/0.50  # Equation resolutions                 : 37
% 0.18/0.50  # Propositional unsat checks           : 0
% 0.18/0.50  #    Propositional check models        : 0
% 0.18/0.50  #    Propositional check unsatisfiable : 0
% 0.18/0.50  #    Propositional clauses             : 0
% 0.18/0.50  #    Propositional clauses after purity: 0
% 0.18/0.50  #    Propositional unsat core size     : 0
% 0.18/0.50  #    Propositional preprocessing time  : 0.000
% 0.18/0.50  #    Propositional encoding time       : 0.000
% 0.18/0.50  #    Propositional solver time         : 0.000
% 0.18/0.50  #    Success case prop preproc time    : 0.000
% 0.18/0.50  #    Success case prop encoding time   : 0.000
% 0.18/0.50  #    Success case prop solver time     : 0.000
% 0.18/0.50  # Current number of processed clauses  : 557
% 0.18/0.50  #    Positive orientable unit clauses  : 46
% 0.18/0.50  #    Positive unorientable unit clauses: 0
% 0.18/0.50  #    Negative unit clauses             : 13
% 0.18/0.50  #    Non-unit-clauses                  : 498
% 0.18/0.50  # Current number of unprocessed clauses: 12816
% 0.18/0.50  # ...number of literals in the above   : 50799
% 0.18/0.50  # Current number of archived formulas  : 0
% 0.18/0.50  # Current number of archived clauses   : 170
% 0.18/0.50  # Clause-clause subsumption calls (NU) : 63210
% 0.18/0.50  # Rec. Clause-clause subsumption calls : 46566
% 0.18/0.50  # Non-unit clause-clause subsumptions  : 1622
% 0.18/0.50  # Unit Clause-clause subsumption calls : 1770
% 0.18/0.50  # Rewrite failures with RHS unbound    : 0
% 0.18/0.50  # BW rewrite match attempts            : 30
% 0.18/0.50  # BW rewrite match successes           : 13
% 0.18/0.50  # Condensation attempts                : 0
% 0.18/0.50  # Condensation successes               : 0
% 0.18/0.50  # Termbank termtop insertions          : 81954
% 0.18/0.50  
% 0.18/0.50  # -------------------------------------------------
% 0.18/0.50  # User time                : 0.156 s
% 0.18/0.50  # System time              : 0.009 s
% 0.18/0.50  # Total time               : 0.165 s
% 0.18/0.50  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
