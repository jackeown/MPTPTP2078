%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:42 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 205 expanded)
%              Number of clauses        :   41 (  69 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  238 (1386 expanded)
%              Number of equality atoms :   38 ( 146 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_funct_2)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(t186_funct_2,axiom,(
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
                      | k1_funct_1(k8_funct_2(X2,X3,X1,X4,X5),X6) = k7_partfun1(X1,X5,k1_funct_1(X4,X6)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

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
                         => k3_funct_2(X2,X3,k8_funct_2(X2,X1,X3,X4,X5),X6) = k7_partfun1(X3,X5,k3_funct_2(X2,X1,X4,X6)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t193_funct_2])).

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
    & k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk3_0,esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_14,plain,(
    ! [X26,X27,X28,X29] :
      ( v1_xboole_0(X26)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,X26,X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ m1_subset_1(X29,X26)
      | k3_funct_2(X26,X27,X28,X29) = k1_funct_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

fof(c_0_15,plain,(
    ! [X30,X31,X32,X33,X34,X35] :
      ( v1_xboole_0(X32)
      | ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,X31,X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | ~ v1_funct_1(X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X30)))
      | ~ m1_subset_1(X35,X31)
      | ~ r1_tarski(k2_relset_1(X31,X32,X33),k1_relset_1(X32,X30,X34))
      | X31 = k1_xboole_0
      | k1_funct_1(k8_funct_2(X31,X32,X30,X33,X34),X35) = k7_partfun1(X30,X34,k1_funct_1(X33,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t186_funct_2])])])])).

fof(c_0_16,plain,(
    ! [X10,X11,X12] :
      ( ( v4_relat_1(X12,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( v5_relat_1(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_17,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_18,negated_conjecture,
    ( k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) != k7_partfun1(esk3_0,esk5_0,k3_funct_2(esk2_0,esk1_0,esk4_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | X3 = k1_xboole_0
    | k1_funct_1(k8_funct_2(X3,X1,X5,X2,X4),X6) = k7_partfun1(X5,X4,k1_funct_1(X2,X6))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
    | ~ m1_subset_1(X6,X3)
    | ~ r1_tarski(k2_relset_1(X3,X1,X2),k1_relset_1(X1,X5,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | k1_relset_1(X23,X24,X25) = k1_relat_1(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( ~ v1_partfun1(X14,X13)
        | k1_relat_1(X14) = X13
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X13) )
      & ( k1_relat_1(X14) != X13
        | v1_partfun1(X14,X13)
        | ~ v1_relat_1(X14)
        | ~ v4_relat_1(X14,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | m1_subset_1(k2_relset_1(X15,X16,X17),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

cnf(c_0_32,negated_conjecture,
    ( k7_partfun1(esk3_0,esk5_0,k1_funct_1(esk4_0,esk6_0)) != k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(k8_funct_2(esk2_0,X1,X2,X3,X4),esk6_0) = k7_partfun1(X2,X4,k1_funct_1(X3,esk6_0))
    | esk2_0 = k1_xboole_0
    | v1_xboole_0(X1)
    | ~ r1_tarski(k2_relset_1(esk2_0,X1,X3),k1_relset_1(X1,X2,X4))
    | ~ v1_funct_2(X3,esk2_0,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_partfun1(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v4_relat_1(esk5_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

fof(c_0_40,plain,(
    ! [X36,X37] :
      ( ( ~ m1_subset_1(X36,k1_zfmisc_1(X37))
        | r1_tarski(X36,X37) )
      & ( ~ r1_tarski(X36,X37)
        | m1_subset_1(X36,k1_zfmisc_1(X37)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_41,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(esk2_0,X1,esk3_0,esk4_0,esk5_0),esk6_0) != k3_funct_2(esk2_0,esk3_0,k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r1_tarski(k2_relset_1(esk2_0,X1,esk4_0),k1_relset_1(X1,esk3_0,esk5_0))
    | ~ v1_funct_2(esk4_0,esk2_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_21])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relset_1(esk1_0,esk3_0,esk5_0) = k1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk1_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_relset_1(esk2_0,esk1_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_xboole_0(X1)
    | k1_funct_1(k8_funct_2(esk2_0,X1,esk3_0,esk4_0,esk5_0),esk6_0) != k1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk6_0)
    | ~ r1_tarski(k2_relset_1(esk2_0,X1,esk4_0),k1_relset_1(X1,esk3_0,esk5_0))
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_2(esk4_0,esk2_0,X1)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,X1)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_23])]),c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( k1_relset_1(esk1_0,esk3_0,esk5_0) = esk1_0 ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk2_0,esk1_0,esk4_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_51,plain,(
    ! [X18,X19,X20,X21,X22] :
      ( ( v1_funct_1(k8_funct_2(X18,X19,X20,X21,X22))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X18,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v1_funct_2(k8_funct_2(X18,X19,X20,X21,X22),X18,X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X18,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(k8_funct_2(X18,X19,X20,X21,X22),k1_zfmisc_1(k2_zfmisc_1(X18,X20)))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X18,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_funct_2])])])).

cnf(c_0_52,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),esk2_0,esk3_0)
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_48]),c_0_49]),c_0_20]),c_0_22]),c_0_29])]),c_0_50])).

cnf(c_0_53,plain,
    ( v1_funct_2(k8_funct_2(X1,X2,X3,X4,X5),X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_54,plain,(
    ! [X38] :
      ( ~ v1_xboole_0(X38)
      | X38 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

cnf(c_0_55,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0))
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_20]),c_0_34]),c_0_21]),c_0_29]),c_0_22])])).

cnf(c_0_56,plain,
    ( v1_funct_1(k8_funct_2(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_59,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ m1_subset_1(k8_funct_2(esk2_0,esk1_0,esk3_0,esk4_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_20]),c_0_34]),c_0_21]),c_0_29]),c_0_22])])).

cnf(c_0_60,plain,
    ( m1_subset_1(k8_funct_2(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( o_0_0_xboole_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_20]),c_0_34]),c_0_21]),c_0_29]),c_0_22])])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_58,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_62]),c_0_63])]),
    [proof]).

%------------------------------------------------------------------------------
