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
% DateTime   : Thu Dec  3 11:08:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 200 expanded)
%              Number of clauses        :   38 (  65 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  226 (1372 expanded)
%              Number of equality atoms :   35 ( 143 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t192_funct_2,conjecture,(
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
                       => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
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
                         => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t192_funct_2])).

fof(c_0_13,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk2_0,esk1_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))
    & v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    & m1_subset_1(esk6_0,esk2_0)
    & v1_partfun1(esk5_0,esk1_0)
    & k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X29,X30,X31,X32] :
      ( v1_xboole_0(X29)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X29,X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X32,X29)
      | k3_funct_2(X29,X30,X31,X32) = k1_funct_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_15,negated_conjecture,
    ( k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( v1_xboole_0(X35)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,X34,X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X33)))
      | ~ m1_subset_1(X38,X34)
      | ~ r1_tarski(k2_relset_1(X34,X35,X36),k1_relset_1(X35,X33,X37))
      | X34 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X34,X35,X33,X36,X37),X38) = k1_funct_1(X37,k1_funct_1(X36,X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( v1_funct_1(k8_funct_2(X24,X25,X26,X27,X28))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v1_funct_2(k8_funct_2(X24,X25,X26,X27,X28),X24,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( m1_subset_1(k8_funct_2(X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X24,X26)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X24,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
        | ~ v1_funct_1(X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

cnf(c_0_29,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_17])]),c_0_27])).

cnf(c_0_30,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k1_relset_1(X19,X20,X21) = k1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_34,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_35,plain,
    ( m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X13,X14,X15] :
      ( ( v4_relat_1(X15,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) )
      & ( v5_relat_1(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_38,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X9))
      | v1_relat_1(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_39,plain,(
    ! [X11,X12] : v1_relat_1(k2_zfmisc_1(X11,X12)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_40,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | m1_subset_1(k2_relset_1(X16,X17,X18),k1_zfmisc_1(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_41,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_22]),c_0_23]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_42,negated_conjecture,
    ( k1_relset_1(esk1_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

fof(c_0_43,plain,(
    ! [X22,X23] :
      ( ( ~ v1_partfun1(X23,X22)
        | k1_relat_1(X23) = X22
        | ~ v1_relat_1(X23)
        | ~ v4_relat_1(X23,X22) )
      & ( k1_relat_1(X23) != X22
        | v1_partfun1(X23,X22)
        | ~ v1_relat_1(X23)
        | ~ v4_relat_1(X23,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_44,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_48,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) != k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))
    | ~ r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_partfun1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( v4_relat_1(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_25])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_25]),c_0_46])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_26])).

cnf(c_0_56,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relat_1(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_16]),c_0_22]),c_0_24]),c_0_26]),c_0_17])]),c_0_18])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_60,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_59]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S5PRR_S0Y
% 0.19/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t192_funct_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>![X6]:(m1_subset_1(X6,X2)=>(v1_partfun1(X5,X1)=>k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6)=k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_funct_2)).
% 0.19/0.37  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.19/0.37  fof(t185_funct_2, axiom, ![X1, X2, X3]:(~(v1_xboole_0(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))))=>![X6]:(m1_subset_1(X6,X2)=>(r1_tarski(k2_relset_1(X2,X3,X4),k1_relset_1(X3,X1,X5))=>(X2=k1_xboole_0|k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6)=k1_funct_1(X5,k1_funct_1(X4,X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 0.19/0.37  fof(dt_k8_funct_2, axiom, ![X1, X2, X3, X4, X5]:(((((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X5))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>((v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))&v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3))&m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 0.19/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.37  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.19/0.37  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(c_0_12, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X1))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))=>![X5]:((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))=>![X6]:(m1_subset_1(X6,X2)=>(v1_partfun1(X5,X1)=>k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6)=k1_funct_1(X5,k3_funct_2(X2,X1,X4,X6))))))))), inference(assume_negation,[status(cth)],[t192_funct_2])).
% 0.19/0.37  fof(c_0_13, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk2_0,esk1_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))))&((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))&(m1_subset_1(esk6_0,esk2_0)&(v1_partfun1(esk5_0,esk1_0)&k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.19/0.37  fof(c_0_14, plain, ![X29, X30, X31, X32]:(v1_xboole_0(X29)|~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,X29)|k3_funct_2(X29,X30,X31,X32)=k1_funct_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.19/0.37  cnf(c_0_15, negated_conjecture, (k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_16, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_18, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_19, plain, ![X33, X34, X35, X36, X37, X38]:(v1_xboole_0(X35)|(~v1_funct_1(X36)|~v1_funct_2(X36,X34,X35)|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X33)))|(~m1_subset_1(X38,X34)|(~r1_tarski(k2_relset_1(X34,X35,X36),k1_relset_1(X35,X33,X37))|(X34=k1_xboole_0|k1_funct_1(k8_funct_2(X34,X35,X33,X36,X37),X38)=k1_funct_1(X37,k1_funct_1(X36,X38)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t185_funct_2])])])])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)!=k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))|~v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])]), c_0_18])).
% 0.19/0.37  cnf(c_0_21, plain, (v1_xboole_0(X1)|X3=k1_xboole_0|k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6)=k1_funct_1(X4,k1_funct_1(X2,X6))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))|~m1_subset_1(X6,X3)|~r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk4_0,esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  fof(c_0_28, plain, ![X24, X25, X26, X27, X28]:(((v1_funct_1(k8_funct_2(X24,X25,X26,X27,X28))|(~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))&(v1_funct_2(k8_funct_2(X24,X25,X26,X27,X28),X24,X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))))&(m1_subset_1(k8_funct_2(X24,X25,X26,X27,X28),k1_zfmisc_1(k2_zfmisc_1(X24,X26)))|(~v1_funct_1(X27)|~v1_funct_2(X27,X24,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|~v1_funct_1(X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).
% 0.19/0.37  cnf(c_0_29, negated_conjecture, (esk2_0=k1_xboole_0|k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_17])]), c_0_27])).
% 0.19/0.37  cnf(c_0_30, plain, (v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_31, negated_conjecture, (esk2_0=k1_xboole_0|k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))|~r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.37  cnf(c_0_32, plain, (v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  fof(c_0_33, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k1_relset_1(X19,X20,X21)=k1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.37  cnf(c_0_34, negated_conjecture, (esk2_0=k1_xboole_0|k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))|~m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.37  cnf(c_0_35, plain, (m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_36, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  fof(c_0_37, plain, ![X13, X14, X15]:((v4_relat_1(X15,X13)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))&(v5_relat_1(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.37  fof(c_0_38, plain, ![X9, X10]:(~v1_relat_1(X9)|(~m1_subset_1(X10,k1_zfmisc_1(X9))|v1_relat_1(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.37  fof(c_0_39, plain, ![X11, X12]:v1_relat_1(k2_zfmisc_1(X11,X12)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.37  fof(c_0_40, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|m1_subset_1(k2_relset_1(X16,X17,X18),k1_zfmisc_1(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (esk2_0=k1_xboole_0|k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relset_1(esk1_0,esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_22]), c_0_23]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.37  cnf(c_0_42, negated_conjecture, (k1_relset_1(esk1_0,esk3_0,esk5_0)=k1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.19/0.37  fof(c_0_43, plain, ![X22, X23]:((~v1_partfun1(X23,X22)|k1_relat_1(X23)=X22|(~v1_relat_1(X23)|~v4_relat_1(X23,X22)))&(k1_relat_1(X23)!=X22|v1_partfun1(X23,X22)|(~v1_relat_1(X23)|~v4_relat_1(X23,X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.37  cnf(c_0_44, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.37  cnf(c_0_45, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.37  cnf(c_0_46, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.37  fof(c_0_47, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_48, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (esk2_0=k1_xboole_0|k1_funct_1(esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0))!=k1_funct_1(esk5_0,k1_funct_1(esk4_0,esk6_0))|~r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relat_1(esk5_0))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.37  cnf(c_0_50, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.37  cnf(c_0_51, negated_conjecture, (v1_partfun1(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.37  cnf(c_0_52, negated_conjecture, (v4_relat_1(esk5_0,esk1_0)), inference(spm,[status(thm)],[c_0_44, c_0_25])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_25]), c_0_46])])).
% 0.19/0.37  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.37  cnf(c_0_55, negated_conjecture, (m1_subset_1(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_zfmisc_1(esk1_0))), inference(spm,[status(thm)],[c_0_48, c_0_26])).
% 0.19/0.37  cnf(c_0_56, negated_conjecture, (esk2_0=k1_xboole_0|~r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_relat_1(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_16]), c_0_22]), c_0_24]), c_0_26]), c_0_17])]), c_0_18])).
% 0.19/0.37  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk5_0)=esk1_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.19/0.37  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.37  cnf(c_0_59, negated_conjecture, (esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57]), c_0_58])])).
% 0.19/0.37  cnf(c_0_60, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_59]), c_0_60])]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 62
% 0.19/0.37  # Proof object clause steps            : 38
% 0.19/0.37  # Proof object formula steps           : 24
% 0.19/0.37  # Proof object conjectures             : 28
% 0.19/0.37  # Proof object clause conjectures      : 25
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 23
% 0.19/0.37  # Proof object initial formulas used   : 12
% 0.19/0.37  # Proof object generating inferences   : 12
% 0.19/0.37  # Proof object simplifying inferences  : 47
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 12
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 26
% 0.19/0.37  # Removed in clause preprocessing      : 0
% 0.19/0.37  # Initial clauses in saturation        : 26
% 0.19/0.37  # Processed clauses                    : 77
% 0.19/0.37  # ...of these trivial                  : 0
% 0.19/0.37  # ...subsumed                          : 0
% 0.19/0.37  # ...remaining for further processing  : 77
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 4
% 0.19/0.37  # Backward-rewritten                   : 14
% 0.19/0.37  # Generated clauses                    : 42
% 0.19/0.37  # ...of the previous two non-trivial   : 48
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 41
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 32
% 0.19/0.37  #    Positive orientable unit clauses  : 16
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 1
% 0.19/0.37  #    Non-unit-clauses                  : 15
% 0.19/0.37  # Current number of unprocessed clauses: 15
% 0.19/0.37  # ...number of literals in the above   : 53
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 44
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 523
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 61
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 4
% 0.19/0.37  # Unit Clause-clause subsumption calls : 11
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 3
% 0.19/0.37  # BW rewrite match successes           : 3
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 3145
% 0.19/0.37  
% 0.19/0.37  # -------------------------------------------------
% 0.19/0.37  # User time                : 0.029 s
% 0.19/0.37  # System time              : 0.007 s
% 0.19/0.37  # Total time               : 0.037 s
% 0.19/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
