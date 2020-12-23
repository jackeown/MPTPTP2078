%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1068+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 113 expanded)
%              Number of clauses        :   29 (  40 expanded)
%              Number of leaves         :    8 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 713 expanded)
%              Number of equality atoms :   41 ( 152 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t185_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X2,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ! [X5] :
              ( ( v1_funct_1(X5)
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => ( X2 = k1_xboole_0
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(d12_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
         => ( r1_tarski(k2_relset_1(X1,X2,X4),k1_relset_1(X2,X3,X5))
           => ( X2 = k1_xboole_0
              | k8_funct_2(X1,X2,X3,X4,X5) = k1_partfun1(X1,X2,X2,X3,X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(t21_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ( ( v1_relat_1(X5)
            & v1_funct_1(X5) )
         => ( r2_hidden(X3,X1)
           => ( X2 = k1_xboole_0
              | k1_funct_1(k5_relat_1(X4,X5),X3) = k1_funct_1(X5,k1_funct_1(X4,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X2,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
           => ! [X5] :
                ( ( v1_funct_1(X5)
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) )
               => ! [X6] :
                    ( m1_subset_1(X6,X2)
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => ( X2 = k1_xboole_0
                        | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k1_funct_1(X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t185_funct_2])).

fof(c_0_9,plain,(
    ! [X10,X11,X12,X13,X14] :
      ( ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X10,X11)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X14)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ r1_tarski(k2_relset_1(X10,X11,X13),k1_relset_1(X11,X12,X14))
      | X11 = k1_xboole_0
      | k8_funct_2(X10,X11,X12,X13,X14) = k1_partfun1(X10,X11,X11,X12,X13,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_2])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & m1_subset_1(esk6_0,esk2_0)
    & r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ~ v1_funct_1(X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k1_partfun1(X15,X16,X17,X18,X19,X20) = k5_relat_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_12,plain,
    ( X3 = k1_xboole_0
    | k8_funct_2(X2,X3,X5,X1,X4) = k1_partfun1(X2,X3,X3,X5,X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X2,X3,X1),k1_relset_1(X3,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk1_0,esk4_0,esk5_0) = k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15]),c_0_16]),c_0_17]),c_0_18])])).

fof(c_0_23,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,X21,X22)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | ~ v1_relat_1(X25)
      | ~ v1_funct_1(X25)
      | ~ r2_hidden(X23,X21)
      | X22 = k1_xboole_0
      | k1_funct_1(k5_relat_1(X24,X25),X23) = k1_funct_1(X25,k1_funct_1(X24,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_2])])])).

cnf(c_0_24,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_funct_1(k5_relat_1(esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_25,plain,
    ( X3 = k1_xboole_0
    | k1_funct_1(k5_relat_1(X1,X4),X5) = k1_funct_1(X4,k1_funct_1(X1,X5))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X4)
    | ~ v1_funct_1(X4)
    | ~ r2_hidden(X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_26,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_27,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk6_0,X2)
    | ~ v1_funct_2(esk4_0,X2,X1)
    | ~ v1_relat_1(esk5_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_15]),c_0_16])])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ r2_hidden(esk6_0,X2)
    | ~ v1_funct_2(esk4_0,X2,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_30,plain,(
    ! [X26,X27] :
      ( ~ m1_subset_1(X26,X27)
      | v1_xboole_0(X27)
      | r2_hidden(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_hidden(esk6_0,esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_18]),c_0_14])])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_34,plain,(
    ! [X28] :
      ( ~ v1_xboole_0(X28)
      | X28 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_35,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(esk2_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_xboole_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_38]),c_0_39])).

cnf(c_0_43,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_42]),c_0_43])]),
    [proof]).

%------------------------------------------------------------------------------
