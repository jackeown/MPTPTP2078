%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:44 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   99 (1731 expanded)
%              Number of clauses        :   70 ( 680 expanded)
%              Number of leaves         :   14 ( 421 expanded)
%              Depth                    :   18
%              Number of atoms          :  479 (12910 expanded)
%              Number of equality atoms :   96 (2385 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   55 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_tmap_1,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ( r1_subset_1(X3,X4)
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,X3,X2)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,X4,X2)
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                           => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                              & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(d1_tmap_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & m1_subset_1(X3,k1_zfmisc_1(X1)) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,X4,X2)
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                         => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2)
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) )
                               => ( X7 = k1_tmap_1(X1,X2,X3,X4,X5,X6)
                                <=> ( k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3) = X5
                                    & k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4) = X6 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(dt_k1_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X3,k1_zfmisc_1(X1))
        & ~ v1_xboole_0(X4)
        & m1_subset_1(X4,k1_zfmisc_1(X1))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X3,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X4,X2)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
     => ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
        & v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
        & m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( ~ v1_xboole_0(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X1)) )
               => ! [X4] :
                    ( ( ~ v1_xboole_0(X4)
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                   => ( r1_subset_1(X3,X4)
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,X3,X2)
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,X4,X2)
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                             => ( k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4)) = k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3) = X5
                                & k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4) = X6 ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_tmap_1])).

fof(c_0_15,plain,(
    ! [X24,X25] :
      ( ( ~ r1_subset_1(X24,X25)
        | r1_xboole_0(X24,X25)
        | v1_xboole_0(X24)
        | v1_xboole_0(X25) )
      & ( ~ r1_xboole_0(X24,X25)
        | r1_subset_1(X24,X25)
        | v1_xboole_0(X24)
        | v1_xboole_0(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
    & r1_subset_1(esk3_0,esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk2_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))
    & ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
      | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
      | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ r1_xboole_0(X10,X11)
      | r1_xboole_0(X11,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_18,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X17,X18,X19] :
      ( ~ v1_relat_1(X19)
      | ~ r1_xboole_0(X17,X18)
      | k7_relat_1(k7_relat_1(X19,X17),X18) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_26,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_27,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v4_relat_1(X21,X20)
      | X21 = k7_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_32,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ( k7_relat_1(X23,X22) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X23),X22)
        | ~ v1_relat_1(X23) )
      & ( ~ r1_xboole_0(k1_relat_1(X23),X22)
        | k7_relat_1(X23,X22) = k1_xboole_0
        | ~ v1_relat_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_38,negated_conjecture,
    ( k7_relat_1(k7_relat_1(esk6_0,esk4_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k7_relat_1(esk6_0,esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_34])])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k7_relat_1(esk6_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_43,plain,(
    ! [X32,X33,X34,X35] :
      ( ~ v1_funct_1(X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | k2_partfun1(X32,X33,X34,X35) = k7_relat_1(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk6_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_42])).

cnf(c_0_47,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_49,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk3_0,k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk5_0,esk3_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_45]),c_0_46])])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_42]),c_0_48])])).

fof(c_0_53,plain,(
    ! [X36,X37,X38,X39,X40,X41,X42] :
      ( ( k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X38) = X40
        | X42 != k1_tmap_1(X36,X37,X38,X39,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,k4_subset_1(X36,X38,X39),X37)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X36,X38,X39),X37)))
        | k2_partfun1(X38,X37,X40,k9_subset_1(X36,X38,X39)) != k2_partfun1(X39,X37,X41,k9_subset_1(X36,X38,X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X37)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X37)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X36))
        | v1_xboole_0(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
        | v1_xboole_0(X37)
        | v1_xboole_0(X36) )
      & ( k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X39) = X41
        | X42 != k1_tmap_1(X36,X37,X38,X39,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,k4_subset_1(X36,X38,X39),X37)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X36,X38,X39),X37)))
        | k2_partfun1(X38,X37,X40,k9_subset_1(X36,X38,X39)) != k2_partfun1(X39,X37,X41,k9_subset_1(X36,X38,X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X37)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X37)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X36))
        | v1_xboole_0(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
        | v1_xboole_0(X37)
        | v1_xboole_0(X36) )
      & ( k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X38) != X40
        | k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X39) != X41
        | X42 = k1_tmap_1(X36,X37,X38,X39,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,k4_subset_1(X36,X38,X39),X37)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X36,X38,X39),X37)))
        | k2_partfun1(X38,X37,X40,k9_subset_1(X36,X38,X39)) != k2_partfun1(X39,X37,X41,k9_subset_1(X36,X38,X39))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X37)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X37)))
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X37)))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X36))
        | v1_xboole_0(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X36))
        | v1_xboole_0(X37)
        | v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_54,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( ( v1_funct_1(k1_tmap_1(X43,X44,X45,X46,X47,X48))
        | v1_xboole_0(X43)
        | v1_xboole_0(X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))) )
      & ( v1_funct_2(k1_tmap_1(X43,X44,X45,X46,X47,X48),k4_subset_1(X43,X45,X46),X44)
        | v1_xboole_0(X43)
        | v1_xboole_0(X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))) )
      & ( m1_subset_1(k1_tmap_1(X43,X44,X45,X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44)))
        | v1_xboole_0(X43)
        | v1_xboole_0(X44)
        | v1_xboole_0(X45)
        | ~ m1_subset_1(X45,k1_zfmisc_1(X43))
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X43))
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,X45,X44)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X44)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_55,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X12))
      | k9_subset_1(X12,X13,X14) = k3_xboole_0(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_56,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | k7_relat_1(X16,X15) = k7_relat_1(X16,k3_xboole_0(k1_relat_1(X16),X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_57,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk3_0),k1_relat_1(esk6_0)) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X7,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X2,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk6_0),esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_44])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_69,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk5_0),X1)
    | k2_partfun1(esk3_0,esk2_0,esk5_0,X1) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_52]),c_0_46])])).

cnf(c_0_70,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_relat_1(esk6_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_46]),c_0_52]),c_0_59]),c_0_52])).

cnf(c_0_71,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]),c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk4_0) = k3_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) = X6
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | X5 != k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_1(X7)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_41]),c_0_34])])).

cnf(c_0_76,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_68])])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(esk5_0),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_78,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),esk4_0) = X4
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk4_0)) != k2_partfun1(esk4_0,X2,X4,k3_xboole_0(X1,esk4_0))
    | ~ v1_funct_2(X4,esk4_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_65])]),c_0_73]),c_0_20])).

cnf(c_0_79,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_24])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_81,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_61]),c_0_62]),c_0_63])).

cnf(c_0_82,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_83,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k3_xboole_0(k1_relat_1(esk5_0),k1_relat_1(esk6_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk4_0) = X3
    | v1_xboole_0(X1)
    | k2_partfun1(esk3_0,X1,X2,k1_xboole_0) != k2_partfun1(esk4_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk4_0,X1)
    | ~ v1_funct_2(X2,esk3_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),c_0_21])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_87,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk4_0)) != k2_partfun1(esk4_0,X2,X4,k3_xboole_0(X1,esk4_0))
    | ~ v1_funct_2(X4,esk4_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_72]),c_0_65])]),c_0_73]),c_0_20])).

cnf(c_0_89,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0
    | k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_72]),c_0_79]),c_0_72]),c_0_79]),c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_84]),c_0_52]),c_0_52]),c_0_70]),c_0_46])])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,X1,esk6_0),esk4_0) = esk6_0
    | k2_partfun1(esk3_0,esk2_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_83]),c_0_86]),c_0_68]),c_0_30])]),c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk3_0) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(esk3_0,X1,X2,k1_xboole_0) != k2_partfun1(esk4_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk4_0,X1)
    | ~ v1_funct_2(X2,esk3_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_79]),c_0_80])]),c_0_21])).

cnf(c_0_94,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90])])).

cnf(c_0_95,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_90]),c_0_92]),c_0_48]),c_0_42])])).

cnf(c_0_96,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,X1),esk3_0) = esk5_0
    | k2_partfun1(esk4_0,esk2_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk4_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_90]),c_0_92]),c_0_48]),c_0_42])]),c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_95])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_83]),c_0_86]),c_0_68]),c_0_30])]),c_0_97]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.50  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.029 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.19/0.50  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.19/0.50  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.19/0.50  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 0.19/0.50  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.50  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.50  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.19/0.50  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.19/0.50  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.50  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.19/0.50  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.19/0.50  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.19/0.50  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.19/0.50  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.19/0.50  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.19/0.50  fof(c_0_15, plain, ![X24, X25]:((~r1_subset_1(X24,X25)|r1_xboole_0(X24,X25)|(v1_xboole_0(X24)|v1_xboole_0(X25)))&(~r1_xboole_0(X24,X25)|r1_subset_1(X24,X25)|(v1_xboole_0(X24)|v1_xboole_0(X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.19/0.50  fof(c_0_16, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)))&(r1_subset_1(esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.50  fof(c_0_17, plain, ![X10, X11]:(~r1_xboole_0(X10,X11)|r1_xboole_0(X11,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.19/0.50  cnf(c_0_18, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.50  cnf(c_0_19, negated_conjecture, (r1_subset_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_20, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  fof(c_0_22, plain, ![X17, X18, X19]:(~v1_relat_1(X19)|(~r1_xboole_0(X17,X18)|k7_relat_1(k7_relat_1(X19,X17),X18)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 0.19/0.50  cnf(c_0_23, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.50  cnf(c_0_24, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])).
% 0.19/0.50  fof(c_0_25, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.50  fof(c_0_26, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.50  cnf(c_0_27, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_28, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.50  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  fof(c_0_31, plain, ![X20, X21]:(~v1_relat_1(X21)|~v4_relat_1(X21,X20)|X21=k7_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.19/0.50  cnf(c_0_32, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  cnf(c_0_33, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.50  cnf(c_0_34, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.50  cnf(c_0_35, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.50  cnf(c_0_36, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.19/0.50  fof(c_0_37, plain, ![X22, X23]:((k7_relat_1(X23,X22)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X23),X22)|~v1_relat_1(X23))&(~r1_xboole_0(k1_relat_1(X23),X22)|k7_relat_1(X23,X22)=k1_xboole_0|~v1_relat_1(X23))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.19/0.50  cnf(c_0_38, negated_conjecture, (k7_relat_1(k7_relat_1(esk6_0,esk4_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.50  cnf(c_0_39, negated_conjecture, (k7_relat_1(esk6_0,esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_34])])).
% 0.19/0.50  cnf(c_0_40, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.50  cnf(c_0_41, negated_conjecture, (k7_relat_1(esk6_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  fof(c_0_43, plain, ![X32, X33, X34, X35]:(~v1_funct_1(X34)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|k2_partfun1(X32,X33,X34,X35)=k7_relat_1(X34,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.50  cnf(c_0_44, negated_conjecture, (r1_xboole_0(k1_relat_1(esk6_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_34])])).
% 0.19/0.50  cnf(c_0_45, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_42])).
% 0.19/0.50  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_42])).
% 0.19/0.50  cnf(c_0_47, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.50  cnf(c_0_48, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  fof(c_0_49, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.19/0.50  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk3_0,k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_44])).
% 0.19/0.50  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk5_0,esk3_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_45]), c_0_46])])).
% 0.19/0.50  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_42]), c_0_48])])).
% 0.19/0.50  fof(c_0_53, plain, ![X36, X37, X38, X39, X40, X41, X42]:(((k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X38)=X40|X42!=k1_tmap_1(X36,X37,X38,X39,X40,X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,k4_subset_1(X36,X38,X39),X37)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X36,X38,X39),X37))))|k2_partfun1(X38,X37,X40,k9_subset_1(X36,X38,X39))!=k2_partfun1(X39,X37,X41,k9_subset_1(X36,X38,X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X37)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X37))))|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X37)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X37))))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(X36)))|(v1_xboole_0(X38)|~m1_subset_1(X38,k1_zfmisc_1(X36)))|v1_xboole_0(X37)|v1_xboole_0(X36))&(k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X39)=X41|X42!=k1_tmap_1(X36,X37,X38,X39,X40,X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,k4_subset_1(X36,X38,X39),X37)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X36,X38,X39),X37))))|k2_partfun1(X38,X37,X40,k9_subset_1(X36,X38,X39))!=k2_partfun1(X39,X37,X41,k9_subset_1(X36,X38,X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X37)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X37))))|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X37)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X37))))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(X36)))|(v1_xboole_0(X38)|~m1_subset_1(X38,k1_zfmisc_1(X36)))|v1_xboole_0(X37)|v1_xboole_0(X36)))&(k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X38)!=X40|k2_partfun1(k4_subset_1(X36,X38,X39),X37,X42,X39)!=X41|X42=k1_tmap_1(X36,X37,X38,X39,X40,X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,k4_subset_1(X36,X38,X39),X37)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X36,X38,X39),X37))))|k2_partfun1(X38,X37,X40,k9_subset_1(X36,X38,X39))!=k2_partfun1(X39,X37,X41,k9_subset_1(X36,X38,X39))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X37)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X37))))|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X37)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X37))))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(X36)))|(v1_xboole_0(X38)|~m1_subset_1(X38,k1_zfmisc_1(X36)))|v1_xboole_0(X37)|v1_xboole_0(X36))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.19/0.50  fof(c_0_54, plain, ![X43, X44, X45, X46, X47, X48]:(((v1_funct_1(k1_tmap_1(X43,X44,X45,X46,X47,X48))|(v1_xboole_0(X43)|v1_xboole_0(X44)|v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43))|v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43))|~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))|~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))))&(v1_funct_2(k1_tmap_1(X43,X44,X45,X46,X47,X48),k4_subset_1(X43,X45,X46),X44)|(v1_xboole_0(X43)|v1_xboole_0(X44)|v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43))|v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43))|~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))|~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44))))))&(m1_subset_1(k1_tmap_1(X43,X44,X45,X46,X47,X48),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X43,X45,X46),X44)))|(v1_xboole_0(X43)|v1_xboole_0(X44)|v1_xboole_0(X45)|~m1_subset_1(X45,k1_zfmisc_1(X43))|v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X43))|~v1_funct_1(X47)|~v1_funct_2(X47,X45,X44)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X44)))|~v1_funct_1(X48)|~v1_funct_2(X48,X46,X44)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.19/0.50  fof(c_0_55, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X12))|k9_subset_1(X12,X13,X14)=k3_xboole_0(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.19/0.50  fof(c_0_56, plain, ![X15, X16]:(~v1_relat_1(X16)|k7_relat_1(X16,X15)=k7_relat_1(X16,k3_xboole_0(k1_relat_1(X16),X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.19/0.50  cnf(c_0_57, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.50  cnf(c_0_58, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk3_0),k1_relat_1(esk6_0))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_50])).
% 0.19/0.50  cnf(c_0_59, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.50  cnf(c_0_60, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.50  cnf(c_0_61, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_62, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_63, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.50  cnf(c_0_64, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.50  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_66, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.50  cnf(c_0_67, negated_conjecture, (k3_xboole_0(k1_relat_1(esk6_0),esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_44])).
% 0.19/0.50  cnf(c_0_68, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_69, negated_conjecture, (r1_xboole_0(k1_relat_1(esk5_0),X1)|k2_partfun1(esk3_0,esk2_0,esk5_0,X1)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_52]), c_0_46])])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k1_relat_1(esk6_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_46]), c_0_52]), c_0_59]), c_0_52])).
% 0.19/0.50  cnf(c_0_71, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_60]), c_0_61]), c_0_62]), c_0_63])).
% 0.19/0.50  cnf(c_0_72, negated_conjecture, (k9_subset_1(esk1_0,X1,esk4_0)=k3_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.19/0.50  cnf(c_0_73, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_74, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.50  cnf(c_0_75, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_41]), c_0_34])])).
% 0.19/0.50  cnf(c_0_76, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_30]), c_0_68])])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (r1_xboole_0(k1_relat_1(esk5_0),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.19/0.50  cnf(c_0_78, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),esk4_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk4_0))!=k2_partfun1(esk4_0,X2,X4,k3_xboole_0(X1,esk4_0))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_65])]), c_0_73]), c_0_20])).
% 0.19/0.50  cnf(c_0_79, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_24])).
% 0.19/0.50  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_81, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_61]), c_0_62]), c_0_63])).
% 0.19/0.50  cnf(c_0_82, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_83, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.19/0.50  cnf(c_0_84, negated_conjecture, (k3_xboole_0(k1_relat_1(esk5_0),k1_relat_1(esk6_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_77])).
% 0.19/0.50  cnf(c_0_85, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk4_0)=X3|v1_xboole_0(X1)|k2_partfun1(esk3_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk4_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk4_0,X1)|~v1_funct_2(X2,esk3_0,X1)|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])]), c_0_21])).
% 0.19/0.50  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_87, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_88, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk4_0))!=k2_partfun1(esk4_0,X2,X4,k3_xboole_0(X1,esk4_0))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_72]), c_0_65])]), c_0_73]), c_0_20])).
% 0.19/0.50  cnf(c_0_89, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0|k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_72]), c_0_79]), c_0_72]), c_0_79]), c_0_83])).
% 0.19/0.50  cnf(c_0_90, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_84]), c_0_52]), c_0_52]), c_0_70]), c_0_46])])).
% 0.19/0.50  cnf(c_0_91, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,X1,esk6_0),esk4_0)=esk6_0|k2_partfun1(esk3_0,esk2_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk3_0,esk2_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_83]), c_0_86]), c_0_68]), c_0_30])]), c_0_87])).
% 0.19/0.50  cnf(c_0_92, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_93, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk3_0)=X2|v1_xboole_0(X1)|k2_partfun1(esk3_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk4_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk4_0,X1)|~v1_funct_2(X2,esk3_0,X1)|~v1_funct_1(X3)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_79]), c_0_80])]), c_0_21])).
% 0.19/0.50  cnf(c_0_94, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_89, c_0_90])])).
% 0.19/0.50  cnf(c_0_95, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_90]), c_0_92]), c_0_48]), c_0_42])])).
% 0.19/0.50  cnf(c_0_96, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,X1),esk3_0)=esk5_0|k2_partfun1(esk4_0,esk2_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk4_0,esk2_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_90]), c_0_92]), c_0_48]), c_0_42])]), c_0_87])).
% 0.19/0.50  cnf(c_0_97, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94, c_0_95])])).
% 0.19/0.50  cnf(c_0_98, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_83]), c_0_86]), c_0_68]), c_0_30])]), c_0_97]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 99
% 0.19/0.50  # Proof object clause steps            : 70
% 0.19/0.50  # Proof object formula steps           : 29
% 0.19/0.50  # Proof object conjectures             : 55
% 0.19/0.50  # Proof object clause conjectures      : 52
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 30
% 0.19/0.50  # Proof object initial formulas used   : 14
% 0.19/0.50  # Proof object generating inferences   : 32
% 0.19/0.50  # Proof object simplifying inferences  : 78
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 14
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 35
% 0.19/0.50  # Removed in clause preprocessing      : 0
% 0.19/0.50  # Initial clauses in saturation        : 35
% 0.19/0.50  # Processed clauses                    : 1498
% 0.19/0.50  # ...of these trivial                  : 10
% 0.19/0.50  # ...subsumed                          : 708
% 0.19/0.50  # ...remaining for further processing  : 780
% 0.19/0.50  # Other redundant clauses eliminated   : 4
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 0
% 0.19/0.50  # Backward-rewritten                   : 45
% 0.19/0.50  # Generated clauses                    : 2125
% 0.19/0.50  # ...of the previous two non-trivial   : 1902
% 0.19/0.50  # Contextual simplify-reflections      : 6
% 0.19/0.50  # Paramodulations                      : 2111
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 15
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
% 0.19/0.50  # Current number of processed clauses  : 697
% 0.19/0.50  #    Positive orientable unit clauses  : 189
% 0.19/0.50  #    Positive unorientable unit clauses: 2
% 0.19/0.50  #    Negative unit clauses             : 5
% 0.19/0.50  #    Non-unit-clauses                  : 501
% 0.19/0.50  # Current number of unprocessed clauses: 426
% 0.19/0.50  # ...number of literals in the above   : 1213
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 80
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 53333
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 25656
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 714
% 0.19/0.50  # Unit Clause-clause subsumption calls : 5311
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 1328
% 0.19/0.50  # BW rewrite match successes           : 31
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 88580
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.152 s
% 0.19/0.50  # System time              : 0.006 s
% 0.19/0.50  # Total time               : 0.158 s
% 0.19/0.50  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
