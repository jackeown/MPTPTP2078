%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : funct_2__t162_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:34 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   20 ( 210 expanded)
%              Number of clauses        :   14 (  75 expanded)
%              Number of leaves         :    3 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 ( 731 expanded)
%              Number of equality atoms :   22 ( 242 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t162_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k5_partfun1(X1,X1,k3_partfun1(X2,X1,X1)) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t162_funct_2.p',t162_funct_2)).

fof(t161_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => k5_partfun1(X1,X2,k3_partfun1(X3,X1,X2)) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t162_funct_2.p',t161_funct_2)).

fof(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t162_funct_2.p',d2_xboole_0)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => k5_partfun1(X1,X1,k3_partfun1(X2,X1,X1)) = k1_tarski(X2) ) ),
    inference(assume_negation,[status(cth)],[t162_funct_2])).

fof(c_0_4,plain,(
    ! [X37,X38,X39] :
      ( ( X38 = k1_xboole_0
        | k5_partfun1(X37,X38,k3_partfun1(X39,X37,X38)) = k1_tarski(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( X37 != k1_xboole_0
        | k5_partfun1(X37,X38,k3_partfun1(X39,X37,X38)) = k1_tarski(X39)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,X37,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t161_funct_2])])])).

fof(c_0_5,negated_conjecture,
    ( v1_funct_1(esk2_0)
    & v1_funct_2(esk2_0,esk1_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0)))
    & k5_partfun1(esk1_0,esk1_0,k3_partfun1(esk2_0,esk1_0,esk1_0)) != k1_tarski(esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_3])])])).

cnf(c_0_6,plain,
    ( X1 = k1_xboole_0
    | k5_partfun1(X2,X1,k3_partfun1(X3,X2,X1)) = k1_tarski(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(split_conjunct,[status(thm)],[d2_xboole_0])).

cnf(c_0_8,negated_conjecture,
    ( k5_partfun1(esk1_0,esk1_0,k3_partfun1(esk2_0,esk1_0,esk1_0)) != k1_tarski(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(X3,X1,X2)) = k1_tarski(X3)
    | X2 = o_0_0_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(rw,[status(thm)],[c_0_6,c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk2_0,esk1_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( esk1_0 = o_0_0_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_14,plain,
    ( k5_partfun1(X1,X2,k3_partfun1(X3,X1,X2)) = k1_tarski(X3)
    | X1 != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_15,negated_conjecture,
    ( k5_partfun1(o_0_0_xboole_0,o_0_0_xboole_0,k3_partfun1(esk2_0,o_0_0_xboole_0,o_0_0_xboole_0)) != k1_tarski(esk2_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_8,c_0_13]),c_0_13]),c_0_13]),c_0_13])).

cnf(c_0_16,plain,
    ( k5_partfun1(o_0_0_xboole_0,X1,k3_partfun1(X2,o_0_0_xboole_0,X1)) = k1_tarski(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
    | ~ v1_funct_2(X2,o_0_0_xboole_0,X1)
    | ~ v1_funct_1(X2) ),
    inference(er,[status(thm)],[inference(rw,[status(thm)],[c_0_14,c_0_7])])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk2_0,o_0_0_xboole_0,o_0_0_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_13]),c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,o_0_0_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_10,c_0_13]),c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_12])]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
