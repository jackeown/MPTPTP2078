%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1070+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:41 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 711 expanded)
%              Number of clauses        :   69 ( 254 expanded)
%              Number of leaves         :   15 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  371 (4938 expanded)
%              Number of equality atoms :   49 ( 141 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t187_funct_2,conjecture,(
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
                  ( ( v1_funct_1(X6)
                    & v1_funct_2(X6,X2,X2)
                    & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) )
                 => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                   => r2_funct_2(X2,X1,k1_partfun1(X2,X2,X2,X1,X6,k8_funct_2(X2,X3,X1,X4,X5)),k8_funct_2(X2,X3,X1,k1_partfun1(X2,X2,X2,X3,X6,X4),X5)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t55_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t45_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(fc4_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X1)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v1_funct_1(k5_relat_1(X4,X3))
        & v1_funct_2(k5_relat_1(X4,X3),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(c_0_15,negated_conjecture,(
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
                    ( ( v1_funct_1(X6)
                      & v1_funct_2(X6,X2,X2)
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) )
                   => ( r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))
                     => r2_funct_2(X2,X1,k1_partfun1(X2,X2,X2,X1,X6,k8_funct_2(X2,X3,X1,X4,X5)),k8_funct_2(X2,X3,X1,k1_partfun1(X2,X2,X2,X3,X6,X4),X5)) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t187_funct_2])).

fof(c_0_16,plain,(
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

fof(c_0_17,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk2_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0))
    & ~ r2_funct_2(esk2_0,esk1_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk1_0,esk6_0,k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0)),k8_funct_2(esk2_0,esk3_0,esk1_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk3_0,esk6_0,esk4_0),esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( ~ v1_funct_1(X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k1_partfun1(X30,X31,X32,X33,X34,X35) = k5_relat_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_19,plain,
    ( X3 = k1_xboole_0
    | k8_funct_2(X2,X3,X5,X1,X4) = k1_partfun1(X2,X3,X3,X5,X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ r1_tarski(k2_relset_1(X2,X3,X1),k1_relset_1(X3,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk3_0,esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_26,plain,(
    ! [X15,X16,X17,X18,X19,X20] :
      ( ( v1_funct_1(k1_partfun1(X15,X16,X17,X18,X19,X20))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(k1_partfun1(X15,X16,X17,X18,X19,X20),k1_zfmisc_1(k2_zfmisc_1(X15,X18)))
        | ~ v1_funct_1(X19)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X20)
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_27,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk1_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk1_0,esk6_0,k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0)),k8_funct_2(esk2_0,esk3_0,esk1_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk3_0,esk6_0,esk4_0),esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X21,X22,X23,X24,X25] :
      ( ( v1_funct_1(k8_funct_2(X21,X22,X23,X24,X25))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(k8_funct_2(X21,X22,X23,X24,X25),X21,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( m1_subset_1(k8_funct_2(X21,X22,X23,X24,X25),k1_zfmisc_1(k2_zfmisc_1(X21,X23)))
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( k1_partfun1(esk2_0,esk3_0,esk3_0,esk1_0,esk4_0,esk5_0) = k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_34,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X36,X37,X38] :
      ( ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | k1_relset_1(X36,X37,X38) = k1_relat_1(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_36,plain,(
    ! [X53,X54,X55] :
      ( ~ v1_relat_1(X53)
      | ~ v1_relat_1(X54)
      | ~ v1_relat_1(X55)
      | k5_relat_1(k5_relat_1(X53,X54),X55) = k5_relat_1(X53,k5_relat_1(X54,X55)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_relat_1])])])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk1_0,k1_partfun1(esk2_0,esk2_0,esk2_0,esk1_0,esk6_0,k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0)),k8_funct_2(esk2_0,esk3_0,esk1_0,k5_relat_1(esk6_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_23]),c_0_30]),c_0_25]),c_0_31])])).

cnf(c_0_39,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0) = k5_relat_1(esk4_0,esk5_0)
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_33]),c_0_22]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_41,plain,
    ( m1_subset_1(k5_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X6))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_29])).

cnf(c_0_42,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k2_relset_1(X39,X40,X41) = k2_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_44,plain,
    ( k5_relat_1(k5_relat_1(X1,X2),X3) = k5_relat_1(X1,k5_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_46,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_funct_2(esk2_0,esk1_0,k5_relat_1(esk6_0,k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0)),k8_funct_2(esk2_0,esk3_0,esk1_0,k5_relat_1(esk6_0,esk4_0),esk5_0))
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk3_0,esk1_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk1_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_22])])).

cnf(c_0_50,plain,
    ( k1_partfun1(X1,X2,X2,X3,X4,X5) = k8_funct_2(X1,X2,X3,X4,X5)
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(X1,X2,X4),k1_relat_1(X5))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_42])).

cnf(c_0_51,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,X2),esk5_0) = k5_relat_1(X1,k5_relat_1(X2,esk5_0))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_54,plain,
    ( v1_funct_1(k5_relat_1(X1,X2))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_funct_2(esk2_0,esk1_0,k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),k8_funct_2(esk2_0,esk3_0,esk1_0,k5_relat_1(esk6_0,esk4_0),esk5_0))
    | ~ m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_40]),c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_25]),c_0_23])])).

cnf(c_0_57,plain,
    ( k1_partfun1(X1,X2,X2,X3,X4,X5) = k8_funct_2(X1,X2,X3,X4,X5)
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X5))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( k5_relat_1(k5_relat_1(X1,esk4_0),esk5_0) = k5_relat_1(X1,k5_relat_1(esk4_0,esk5_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,esk4_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_25]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k5_relat_1(X1,esk4_0),k1_zfmisc_1(k2_zfmisc_1(X2,esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_23])])).

fof(c_0_62,plain,(
    ! [X42,X43,X44,X45] :
      ( ( ~ r2_funct_2(X42,X43,X44,X45)
        | X44 = X45
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( X44 != X45
        | r2_funct_2(X42,X43,X44,X45)
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X42,X43)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_63,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_funct_2(esk2_0,esk1_0,k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),k8_funct_2(esk2_0,esk3_0,esk1_0,k5_relat_1(esk6_0,esk4_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_64,plain,
    ( k8_funct_2(X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | X2 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(X4),k1_relat_1(X5))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( k5_relat_1(k5_relat_1(esk6_0,esk4_0),esk5_0) = k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk6_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_31]),c_0_30])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_31]),c_0_30])])).

cnf(c_0_68,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k5_relat_1(X1,esk5_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_24]),c_0_22])])).

fof(c_0_70,plain,(
    ! [X46,X47,X48] :
      ( ~ r1_tarski(X46,X47)
      | ~ r1_tarski(X47,X48)
      | r1_tarski(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),k1_relset_1(esk3_0,esk1_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_51]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r2_funct_2(esk2_0,esk1_0,k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)))
    | ~ r1_tarski(k2_relat_1(k5_relat_1(esk6_0,esk4_0)),k1_relat_1(esk5_0))
    | ~ v1_funct_2(k5_relat_1(esk6_0,esk4_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_22]),c_0_66]),c_0_24]),c_0_67])])).

cnf(c_0_73,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_67]),c_0_65]),c_0_66])])).

cnf(c_0_75,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_67]),c_0_65]),c_0_66])])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_42]),c_0_24])])).

cnf(c_0_78,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(k5_relat_1(esk6_0,esk4_0)),k1_relat_1(esk5_0))
    | ~ v1_funct_2(k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),esk2_0,esk1_0)
    | ~ v1_funct_2(k5_relat_1(esk6_0,esk4_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_75])])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(X1,k1_relat_1(esk5_0))
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

fof(c_0_80,plain,(
    ! [X51,X52] :
      ( ~ v1_relat_1(X51)
      | ~ v1_relat_1(X52)
      | r1_tarski(k2_relat_1(k5_relat_1(X51,X52)),k2_relat_1(X52)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t45_relat_1])])])).

cnf(c_0_81,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ r1_tarski(k2_relat_1(k5_relat_1(esk6_0,esk4_0)),k2_relat_1(esk4_0))
    | ~ v1_funct_2(k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),esk2_0,esk1_0)
    | ~ v1_funct_2(k5_relat_1(esk6_0,esk4_0),esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X1,X2)),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

fof(c_0_83,plain,(
    ! [X26,X27,X28,X29] :
      ( ( v1_funct_1(k5_relat_1(X29,X28))
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) )
      & ( v1_funct_2(k5_relat_1(X29,X28),X26,X27)
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,X26,X26)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X26,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc4_funct_2])])])).

cnf(c_0_84,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_85,plain,(
    ! [X56] :
      ( ~ v1_xboole_0(X56)
      | X56 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_86,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_2(k5_relat_1(esk6_0,k5_relat_1(esk4_0,esk5_0)),esk2_0,esk1_0)
    | ~ v1_funct_2(k5_relat_1(esk6_0,esk4_0),esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_53]),c_0_59])])).

cnf(c_0_87,plain,
    ( v1_funct_2(k5_relat_1(X1,X2),X3,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(esk6_0,esk2_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_89,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_25]),c_0_23])])).

cnf(c_0_90,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(k5_relat_1(esk4_0,esk5_0),esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_40]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_92,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_93,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v1_funct_2(k5_relat_1(esk6_0,esk4_0),esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88]),c_0_89]),c_0_30]),c_0_56]),c_0_31])]),c_0_90])).

cnf(c_0_94,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_96,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_87]),c_0_21]),c_0_88]),c_0_23]),c_0_30]),c_0_25]),c_0_31])])).

cnf(c_0_97,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_92,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_97])]),
    [proof]).

%------------------------------------------------------------------------------
