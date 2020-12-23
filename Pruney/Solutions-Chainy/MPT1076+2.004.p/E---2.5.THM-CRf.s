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
% DateTime   : Thu Dec  3 11:08:16 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 364 expanded)
%              Number of clauses        :   61 ( 124 expanded)
%              Number of leaves         :   19 (  91 expanded)
%              Depth                    :   16
%              Number of atoms          :  380 (2337 expanded)
%              Number of equality atoms :   46 ( 230 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t193_funct_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3,X4] :
              ( ( v1_funct_1(X4)
                & v1_funct_2(X4,X2,X1)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
             => ! [X5] :
                  ( ( v1_funct_1(X5)
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) )
                 => ! [X6] :
                      ( m1_subset_1(X6,X2)
                     => ( v1_partfun1(X5,X1)
                       => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k7_partfun1(X3,X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(cc2_partfun1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2) )
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ~ v1_partfun1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(t176_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( m1_subset_1(X4,X1)
                 => k7_partfun1(X2,X3,X4) = k3_funct_2(X1,X2,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t185_funct_2,axiom,(
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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
        & v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
        & m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(cc1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( v1_funct_1(X3)
          & v1_partfun1(X3,X1) )
       => ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3,X4] :
                ( ( v1_funct_1(X4)
                  & v1_funct_2(X4,X2,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
               => ! [X5] :
                    ( ( v1_funct_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) )
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => ( v1_partfun1(X5,X1)
                         => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k7_partfun1(X3,X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t193_funct_2])).

fof(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & m1_subset_1(esk6_0,esk2_0)
    & v1_partfun1(esk5_0,esk1_0)
    & k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk3_0,esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_21,plain,(
    ! [X45,X46,X47,X48] :
      ( v1_xboole_0(X45)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,X45,X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | ~ m1_subset_1(X48,X45)
      | k3_funct_2(X45,X46,X47,X48) = k1_funct_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_22,plain,(
    ! [X32,X33,X34] :
      ( v1_xboole_0(X32)
      | ~ v1_xboole_0(X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ v1_partfun1(X34,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_partfun1])])])])).

cnf(c_0_23,negated_conjecture,
    ( k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk3_0,esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X49,X50,X51,X52] :
      ( v1_xboole_0(X49)
      | v1_xboole_0(X50)
      | ~ v1_funct_1(X51)
      | ~ v1_funct_2(X51,X49,X50)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))
      | ~ m1_subset_1(X52,X49)
      | k7_partfun1(X50,X51,X52) = k3_funct_2(X49,X50,X51,X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t176_funct_2])])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v1_partfun1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_35,plain,(
    ! [X35,X36,X37] :
      ( ( v1_funct_1(X37)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | v1_xboole_0(X36) )
      & ( v1_partfun1(X37,X35)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X35,X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_36,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_37,plain,(
    ! [X15,X16] : v1_relat_1(k2_zfmisc_1(X15,X16)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_38,negated_conjecture,
    ( k7_partfun1(esk3_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) != k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28])]),c_0_29])).

cnf(c_0_39,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | k7_partfun1(X2,X3,X4) = k3_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),c_0_34])).

fof(c_0_42,plain,(
    ! [X38,X39] :
      ( ( ~ v1_partfun1(X39,X38)
        | k1_relat_1(X39) = X38
        | ~ v1_relat_1(X39)
        | ~ v4_relat_1(X39,X38) )
      & ( k1_relat_1(X39) != X38
        | v1_partfun1(X39,X38)
        | ~ v1_relat_1(X39)
        | ~ v4_relat_1(X39,X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_43,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X20,X21,X22] :
      ( ( v4_relat_1(X22,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( v5_relat_1(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,esk3_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) != k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ v1_funct_2(esk5_0,X1,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(k1_funct_1(esk4_0,esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]),c_0_41])).

cnf(c_0_48,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v1_partfun1(esk4_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_25]),c_0_26]),c_0_27])]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_45])])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(X1)
    | k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v1_funct_2(esk5_0,X1,esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(k1_funct_1(esk4_0,esk6_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_24]),c_0_40])])).

fof(c_0_53,plain,(
    ! [X7,X8] :
      ( ~ r2_hidden(X7,X8)
      | m1_subset_1(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

fof(c_0_54,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ v5_relat_1(X18,X17)
      | ~ v1_funct_1(X18)
      | ~ r2_hidden(X19,k1_relat_1(X18))
      | r2_hidden(k1_funct_1(X18,X19),X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_55,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0
    | ~ v4_relat_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_57,negated_conjecture,
    ( v4_relat_1(esk4_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_27])).

fof(c_0_58,plain,(
    ! [X9,X10] :
      ( ~ m1_subset_1(X9,X10)
      | v1_xboole_0(X10)
      | r2_hidden(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_59,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_2(esk5_0,X1,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ m1_subset_1(k1_funct_1(esk4_0,esk6_0),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_24]),c_0_28])]),c_0_29])).

cnf(c_0_61,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_62,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v5_relat_1(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_27])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X53,X54,X55,X56,X57,X58] :
      ( v1_xboole_0(X55)
      | ~ v1_funct_1(X56)
      | ~ v1_funct_2(X56,X54,X55)
      | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
      | ~ v1_funct_1(X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))
      | ~ m1_subset_1(X58,X54)
      | ~ r1_tarski(k2_relset_1(X54,X55,X56),k1_relset_1(X55,X53,X57))
      | X54 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X54,X55,X53,X56,X57),X58) = k1_funct_1(X57,k1_funct_1(X56,X58)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

fof(c_0_67,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k2_relset_1(X26,X27,X28) = k2_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_68,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( v4_relat_1(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_32]),c_0_45])])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_2(esk5_0,X1,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r2_hidden(k1_funct_1(esk4_0,esk6_0),X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk4_0,X1),esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_26]),c_0_50])]),c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_28]),c_0_29])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k1_funct_1(X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k1_relset_1(esk1_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_32])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_69]),c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_2(esk5_0,esk1_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_32]),c_0_73])]),c_0_34])).

cnf(c_0_79,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,X1,X2,X3,X4),esk6_0) = k1_funct_1(X4,k1_funct_1(X3,esk6_0))
    | esk2_0 = k1_xboole_0
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X3,esk2_0,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(k2_relset_1(esk2_0,X1,X3),k1_relset_1(X1,X2,X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( k2_relset_1(esk2_0,esk1_0,esk4_0) = k2_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( k1_relset_1(esk1_0,esk3_0,esk5_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_76,c_0_77])).

fof(c_0_82,plain,(
    ! [X40,X41,X42,X43,X44] :
      ( ( v1_funct_1(k8_funct_2(X40,X41,X42,X43,X44))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X40,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( v1_funct_2(k8_funct_2(X40,X41,X42,X43,X44),X40,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X40,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( m1_subset_1(k8_funct_2(X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X40,X42)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X40,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | ~ v1_funct_1(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

cnf(c_0_83,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_2(esk5_0,esk1_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(k2_relat_1(esk4_0),esk1_0)
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_25]),c_0_40]),c_0_26]),c_0_80]),c_0_81]),c_0_27]),c_0_32])]),c_0_34])).

cnf(c_0_84,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk1_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(k2_relat_1(esk4_0),esk1_0)
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_25]),c_0_40]),c_0_26]),c_0_32]),c_0_27])])).

cnf(c_0_86,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_87,plain,(
    ! [X29,X30,X31] :
      ( ( v1_funct_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_partfun1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v1_funct_2(X31,X29,X30)
        | ~ v1_funct_1(X31)
        | ~ v1_partfun1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).

cnf(c_0_88,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk1_0,esk3_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk1_0)
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_25]),c_0_40]),c_0_26]),c_0_32]),c_0_27])])).

cnf(c_0_89,plain,
    ( m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_90,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk5_0,esk1_0,esk3_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_25]),c_0_40]),c_0_26]),c_0_32]),c_0_27])])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(esk5_0,esk1_0,X1)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_33]),c_0_40])])).

fof(c_0_93,plain,(
    ! [X13,X14] :
      ( ( ~ v5_relat_1(X14,X13)
        | r1_tarski(k2_relat_1(X14),X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(k2_relat_1(X14),X13)
        | v5_relat_1(X14,X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_94,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(esk4_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_32])])).

cnf(c_0_95,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_63]),c_0_50])])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_96]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.14/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.029 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t193_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>![X6]:(m1_subset_1(X6,X2)=>(v1_partfun1(X5,X1)=>k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6)=k7_partfun1(X3,X5,k3_funct_2(X2,X1,X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_funct_2)).
% 0.14/0.40  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.14/0.40  fof(cc2_partfun1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>~(v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_partfun1)).
% 0.14/0.40  fof(t176_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(m1_subset_1(X4,X1)=>k7_partfun1(X2,X3,X4)=k3_funct_2(X1,X2,X3,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 0.14/0.40  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.14/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.40  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.14/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.40  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.14/0.40  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.14/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.14/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.40  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 0.14/0.40  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.14/0.40  fof(dt_k8_funct_2, axiom, ![X1, X2, X3, X4, X5]:(((((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X5))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))&v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3))&m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 0.14/0.40  fof(cc1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_partfun1(X3,X1))=>(v1_funct_1(X3)&v1_funct_2(X3,X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 0.14/0.40  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.14/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.40  fof(c_0_19, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>![X6]:(m1_subset_1(X6,X2)=>(v1_partfun1(X5,X1)=>k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6)=k7_partfun1(X3,X5,k3_funct_2(X2,X1,X4,X6))))))))), inference(assume_negation,[status(cth)],[t193_funct_2])).
% 0.14/0.40  fof(c_0_20, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))&(m1_subset_1(esk6_0,esk2_0)&(v1_partfun1(esk5_0,esk1_0)&k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k7_partfun1(esk3_0,esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 0.14/0.40  fof(c_0_21, plain, ![X45, X46, X47, X48]:(v1_xboole_0(X45)|~v1_funct_1(X47)|~v1_funct_2(X47,X45,X46)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|~m1_subset_1(X48,X45)|k3_funct_2(X45,X46,X47,X48)=k1_funct_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.14/0.40  fof(c_0_22, plain, ![X32, X33, X34]:(v1_xboole_0(X32)|~v1_xboole_0(X33)|(~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~v1_partfun1(X34,X32))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_partfun1])])])])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k7_partfun1(esk3_0,esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_24, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  fof(c_0_30, plain, ![X49, X50, X51, X52]:(v1_xboole_0(X49)|(v1_xboole_0(X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X50)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50)))|(~m1_subset_1(X52,X49)|k7_partfun1(X50,X51,X52)=k3_funct_2(X49,X50,X51,X52))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t176_funct_2])])])])).
% 0.14/0.40  cnf(c_0_31, plain, (v1_xboole_0(X1)|~v1_xboole_0(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_partfun1(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_33, negated_conjecture, (v1_partfun1(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  fof(c_0_35, plain, ![X35, X36, X37]:((v1_funct_1(X37)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_xboole_0(X36))&(v1_partfun1(X37,X35)|(~v1_funct_1(X37)|~v1_funct_2(X37,X35,X36))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_xboole_0(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.14/0.40  fof(c_0_36, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.40  fof(c_0_37, plain, ![X15, X16]:v1_relat_1(k2_zfmisc_1(X15,X16)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.40  cnf(c_0_38, negated_conjecture, (k7_partfun1(esk3_0,esk5_0,k1_funct_1(esk4_0,esk6_0))!=k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28])]), c_0_29])).
% 0.14/0.40  cnf(c_0_39, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|k7_partfun1(X2,X3,X4)=k3_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.40  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_41, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), c_0_34])).
% 0.14/0.40  fof(c_0_42, plain, ![X38, X39]:((~v1_partfun1(X39,X38)|k1_relat_1(X39)=X38|(~v1_relat_1(X39)|~v4_relat_1(X39,X38)))&(k1_relat_1(X39)!=X38|v1_partfun1(X39,X38)|(~v1_relat_1(X39)|~v4_relat_1(X39,X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.14/0.40  cnf(c_0_43, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.40  cnf(c_0_44, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_45, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.40  fof(c_0_46, plain, ![X20, X21, X22]:((v4_relat_1(X22,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))&(v5_relat_1(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.40  cnf(c_0_47, negated_conjecture, (v1_xboole_0(X1)|k3_funct_2(X1,esk3_0,esk5_0,k1_funct_1(esk4_0,esk6_0))!=k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)|~v1_funct_2(esk5_0,X1,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(k1_funct_1(esk4_0,esk6_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])]), c_0_41])).
% 0.14/0.40  cnf(c_0_48, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.40  cnf(c_0_49, negated_conjecture, (v1_partfun1(esk4_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_25]), c_0_26]), c_0_27])]), c_0_34])).
% 0.14/0.40  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_27]), c_0_45])])).
% 0.14/0.40  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.40  cnf(c_0_52, negated_conjecture, (v1_xboole_0(X1)|k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v1_funct_2(esk5_0,X1,esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(k1_funct_1(esk4_0,esk6_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_24]), c_0_40])])).
% 0.14/0.40  fof(c_0_53, plain, ![X7, X8]:(~r2_hidden(X7,X8)|m1_subset_1(X7,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.14/0.40  fof(c_0_54, plain, ![X17, X18, X19]:(~v1_relat_1(X18)|~v5_relat_1(X18,X17)|~v1_funct_1(X18)|(~r2_hidden(X19,k1_relat_1(X18))|r2_hidden(k1_funct_1(X18,X19),X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.14/0.40  cnf(c_0_55, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0|~v4_relat_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.14/0.40  cnf(c_0_57, negated_conjecture, (v4_relat_1(esk4_0,esk2_0)), inference(spm,[status(thm)],[c_0_51, c_0_27])).
% 0.14/0.40  fof(c_0_58, plain, ![X9, X10]:(~m1_subset_1(X9,X10)|(v1_xboole_0(X10)|r2_hidden(X9,X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.14/0.40  fof(c_0_59, plain, ![X23, X24, X25]:(~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))|k1_relset_1(X23,X24,X25)=k1_relat_1(X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.40  cnf(c_0_60, negated_conjecture, (v1_xboole_0(X1)|k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)|~v1_funct_2(esk5_0,X1,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~m1_subset_1(k1_funct_1(esk4_0,esk6_0),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_24]), c_0_28])]), c_0_29])).
% 0.14/0.40  cnf(c_0_61, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.40  cnf(c_0_62, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.40  cnf(c_0_63, negated_conjecture, (v5_relat_1(esk4_0,esk1_0)), inference(spm,[status(thm)],[c_0_55, c_0_27])).
% 0.14/0.40  cnf(c_0_64, negated_conjecture, (k1_relat_1(esk4_0)=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 0.14/0.40  cnf(c_0_65, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.40  fof(c_0_66, plain, ![X53, X54, X55, X56, X57, X58]:(v1_xboole_0(X55)|(~v1_funct_1(X56)|~v1_funct_2(X56,X54,X55)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))|(~v1_funct_1(X57)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))|(~m1_subset_1(X58,X54)|(~r1_tarski(k2_relset_1(X54,X55,X56),k1_relset_1(X55,X53,X57))|(X54=k1_xboole_0|k1_funct_1(k8_funct_2(X54,X55,X53,X56,X57),X58)=k1_funct_1(X57,k1_funct_1(X56,X58)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.14/0.40  fof(c_0_67, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k2_relset_1(X26,X27,X28)=k2_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.14/0.40  cnf(c_0_68, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.14/0.40  cnf(c_0_69, negated_conjecture, (v4_relat_1(esk5_0,esk1_0)), inference(spm,[status(thm)],[c_0_51, c_0_32])).
% 0.14/0.40  cnf(c_0_70, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_32]), c_0_45])])).
% 0.14/0.40  cnf(c_0_71, negated_conjecture, (v1_xboole_0(X1)|k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)|~v1_funct_2(esk5_0,X1,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~r2_hidden(k1_funct_1(esk4_0,esk6_0),X1)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.14/0.40  cnf(c_0_72, negated_conjecture, (r2_hidden(k1_funct_1(esk4_0,X1),esk1_0)|~r2_hidden(X1,esk2_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_26]), c_0_50])]), c_0_64])).
% 0.14/0.40  cnf(c_0_73, negated_conjecture, (r2_hidden(esk6_0,esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_28]), c_0_29])).
% 0.14/0.40  cnf(c_0_74, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.14/0.40  cnf(c_0_75, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.14/0.40  cnf(c_0_76, negated_conjecture, (k1_relset_1(esk1_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_68, c_0_32])).
% 0.14/0.40  cnf(c_0_77, negated_conjecture, (k1_relat_1(esk5_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_69]), c_0_70])])).
% 0.14/0.40  cnf(c_0_78, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)|~v1_funct_2(esk5_0,esk1_0,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_32]), c_0_73])]), c_0_34])).
% 0.14/0.40  cnf(c_0_79, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,X1,X2,X3,X4),esk6_0)=k1_funct_1(X4,k1_funct_1(X3,esk6_0))|esk2_0=k1_xboole_0|v1_xboole_0(X1)|~v1_funct_2(X3,esk2_0,X1)|~v1_funct_1(X4)|~v1_funct_1(X3)|~r1_tarski(k2_relset_1(esk2_0,X1,X3),k1_relset_1(X1,X2,X4))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_74, c_0_28])).
% 0.14/0.40  cnf(c_0_80, negated_conjecture, (k2_relset_1(esk2_0,esk1_0,esk4_0)=k2_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_75, c_0_27])).
% 0.14/0.40  cnf(c_0_81, negated_conjecture, (k1_relset_1(esk1_0,esk3_0,esk5_0)=esk1_0), inference(rw,[status(thm)],[c_0_76, c_0_77])).
% 0.14/0.40  fof(c_0_82, plain, ![X40, X41, X42, X43, X44]:(((v1_funct_1(k8_funct_2(X40,X41,X42,X43,X44))|(~v1_funct_1(X43)|~v1_funct_2(X43,X40,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))&(v1_funct_2(k8_funct_2(X40,X41,X42,X43,X44),X40,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,X40,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))))))&(m1_subset_1(k8_funct_2(X40,X41,X42,X43,X44),k1_zfmisc_1(k2_zfmisc_1(X40,X42)))|(~v1_funct_1(X43)|~v1_funct_2(X43,X40,X41)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|~v1_funct_1(X44)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).
% 0.14/0.40  cnf(c_0_83, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)|~v1_funct_2(esk5_0,esk1_0,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~r1_tarski(k2_relat_1(esk4_0),esk1_0)|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_25]), c_0_40]), c_0_26]), c_0_80]), c_0_81]), c_0_27]), c_0_32])]), c_0_34])).
% 0.14/0.40  cnf(c_0_84, plain, (v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.14/0.40  cnf(c_0_85, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk5_0,esk1_0,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~r1_tarski(k2_relat_1(esk4_0),esk1_0)|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_25]), c_0_40]), c_0_26]), c_0_32]), c_0_27])])).
% 0.14/0.40  cnf(c_0_86, plain, (v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.14/0.40  fof(c_0_87, plain, ![X29, X30, X31]:((v1_funct_1(X31)|(~v1_funct_1(X31)|~v1_partfun1(X31,X29))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v1_funct_2(X31,X29,X30)|(~v1_funct_1(X31)|~v1_partfun1(X31,X29))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_funct_2])])])).
% 0.14/0.40  cnf(c_0_88, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk5_0,esk1_0,esk3_0)|~r1_tarski(k2_relat_1(esk4_0),esk1_0)|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_25]), c_0_40]), c_0_26]), c_0_32]), c_0_27])])).
% 0.14/0.40  cnf(c_0_89, plain, (m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_82])).
% 0.14/0.40  cnf(c_0_90, plain, (v1_funct_2(X1,X2,X3)|~v1_funct_1(X1)|~v1_partfun1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_87])).
% 0.14/0.40  cnf(c_0_91, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk5_0,esk1_0,esk3_0)|~r1_tarski(k2_relat_1(esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_25]), c_0_40]), c_0_26]), c_0_32]), c_0_27])])).
% 0.14/0.40  cnf(c_0_92, negated_conjecture, (v1_funct_2(esk5_0,esk1_0,X1)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_33]), c_0_40])])).
% 0.14/0.40  fof(c_0_93, plain, ![X13, X14]:((~v5_relat_1(X14,X13)|r1_tarski(k2_relat_1(X14),X13)|~v1_relat_1(X14))&(~r1_tarski(k2_relat_1(X14),X13)|v5_relat_1(X14,X13)|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.14/0.40  cnf(c_0_94, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(k2_relat_1(esk4_0),esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_32])])).
% 0.14/0.40  cnf(c_0_95, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_93])).
% 0.14/0.40  cnf(c_0_96, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_63]), c_0_50])])).
% 0.14/0.40  cnf(c_0_97, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.40  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_96]), c_0_97])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 99
% 0.14/0.40  # Proof object clause steps            : 61
% 0.14/0.40  # Proof object formula steps           : 38
% 0.14/0.40  # Proof object conjectures             : 43
% 0.14/0.40  # Proof object clause conjectures      : 40
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 31
% 0.14/0.40  # Proof object initial formulas used   : 19
% 0.14/0.40  # Proof object generating inferences   : 27
% 0.14/0.40  # Proof object simplifying inferences  : 79
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 19
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 35
% 0.14/0.40  # Removed in clause preprocessing      : 2
% 0.14/0.40  # Initial clauses in saturation        : 33
% 0.14/0.40  # Processed clauses                    : 206
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 55
% 0.14/0.40  # ...remaining for further processing  : 151
% 0.14/0.40  # Other redundant clauses eliminated   : 1
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 4
% 0.14/0.40  # Backward-rewritten                   : 48
% 0.14/0.40  # Generated clauses                    : 235
% 0.14/0.40  # ...of the previous two non-trivial   : 261
% 0.14/0.40  # Contextual simplify-reflections      : 3
% 0.14/0.40  # Paramodulations                      : 234
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 1
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 65
% 0.14/0.40  #    Positive orientable unit clauses  : 15
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 2
% 0.14/0.40  #    Non-unit-clauses                  : 48
% 0.14/0.40  # Current number of unprocessed clauses: 81
% 0.14/0.40  # ...number of literals in the above   : 832
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 85
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 6083
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 247
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 50
% 0.14/0.40  # Unit Clause-clause subsumption calls : 229
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 3
% 0.14/0.40  # BW rewrite match successes           : 3
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 14530
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.053 s
% 0.14/0.40  # System time              : 0.003 s
% 0.14/0.40  # Total time               : 0.057 s
% 0.14/0.40  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
