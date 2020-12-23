%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:39 EST 2020

% Result     : Theorem 19.09s
% Output     : CNFRefutation 19.09s
% Verified   : 
% Statistics : Number of formulae       :  103 (1283 expanded)
%              Number of clauses        :   74 ( 490 expanded)
%              Number of leaves         :   14 ( 315 expanded)
%              Depth                    :   11
%              Number of atoms          :  502 (10039 expanded)
%              Number of equality atoms :   91 (1879 expanded)
%              Maximal formula depth    :   28 (   5 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(symmetry_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
       => r1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(t207_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_xboole_0(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X1),X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

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
    ! [X23,X24] :
      ( ( ~ r1_subset_1(X23,X24)
        | r1_xboole_0(X23,X24)
        | v1_xboole_0(X23)
        | v1_xboole_0(X24) )
      & ( ~ r1_xboole_0(X23,X24)
        | r1_subset_1(X23,X24)
        | v1_xboole_0(X23)
        | v1_xboole_0(X24) ) ) ),
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
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | v1_xboole_0(X26)
      | ~ r1_subset_1(X25,X26)
      | r1_subset_1(X26,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).

fof(c_0_18,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_xboole_0(X18,X19)
      | k7_relat_1(k7_relat_1(X20,X18),X19) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).

cnf(c_0_19,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(k7_relat_1(X17,X15),X16) = k7_relat_1(X17,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_24,plain,(
    ! [X13,X14] : k1_setfam_1(k2_tarski(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_25,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( ( v1_funct_1(k1_tmap_1(X44,X45,X46,X47,X48,X49))
        | v1_xboole_0(X44)
        | v1_xboole_0(X45)
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X44))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X45)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))) )
      & ( v1_funct_2(k1_tmap_1(X44,X45,X46,X47,X48,X49),k4_subset_1(X44,X46,X47),X45)
        | v1_xboole_0(X44)
        | v1_xboole_0(X45)
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X44))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X45)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))) )
      & ( m1_subset_1(k1_tmap_1(X44,X45,X46,X47,X48,X49),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45)))
        | v1_xboole_0(X44)
        | v1_xboole_0(X45)
        | v1_xboole_0(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(X44))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X44))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,X46,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X45)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_26,plain,(
    ! [X11,X12] :
      ( ~ v1_xboole_0(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X8))
      | k9_subset_1(X8,X9,X10) = k3_xboole_0(X9,X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_28,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_partfun1(X33,X34,X35,X36) = k7_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_29,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_30,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_subset_1(X2,X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_34,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] :
      ( ( k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X39) = X41
        | X43 != k1_tmap_1(X37,X38,X39,X40,X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,k4_subset_1(X37,X39,X40),X38)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X37,X39,X40),X38)))
        | k2_partfun1(X39,X38,X41,k9_subset_1(X37,X39,X40)) != k2_partfun1(X40,X38,X42,k9_subset_1(X37,X39,X40))
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X38)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X38)))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X38)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
        | v1_xboole_0(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X37))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
        | v1_xboole_0(X38)
        | v1_xboole_0(X37) )
      & ( k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X40) = X42
        | X43 != k1_tmap_1(X37,X38,X39,X40,X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,k4_subset_1(X37,X39,X40),X38)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X37,X39,X40),X38)))
        | k2_partfun1(X39,X38,X41,k9_subset_1(X37,X39,X40)) != k2_partfun1(X40,X38,X42,k9_subset_1(X37,X39,X40))
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X38)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X38)))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X38)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
        | v1_xboole_0(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X37))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
        | v1_xboole_0(X38)
        | v1_xboole_0(X37) )
      & ( k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X39) != X41
        | k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X40) != X42
        | X43 = k1_tmap_1(X37,X38,X39,X40,X41,X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,k4_subset_1(X37,X39,X40),X38)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X37,X39,X40),X38)))
        | k2_partfun1(X39,X38,X41,k9_subset_1(X37,X39,X40)) != k2_partfun1(X40,X38,X42,k9_subset_1(X37,X39,X40))
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X38)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X38)))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X38)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38)))
        | v1_xboole_0(X40)
        | ~ m1_subset_1(X40,k1_zfmisc_1(X37))
        | v1_xboole_0(X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(X37))
        | v1_xboole_0(X38)
        | v1_xboole_0(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_46,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | ~ v4_relat_1(X22,X21)
      | X22 = k7_relat_1(X22,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_47,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( r1_subset_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_51,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_52,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))
    | ~ v1_funct_2(X6,X3,X1)
    | ~ v1_funct_2(X5,X2,X1)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X4)) ),
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_54,plain,
    ( v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_55,plain,
    ( v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | ~ v1_funct_2(X6,X4,X2)
    | ~ v1_funct_2(X5,X3,X2)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_40,c_0_38])).

cnf(c_0_56,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_35])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_49]),c_0_22]),c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(X1,k1_setfam_1(k2_tarski(esk3_0,esk4_0))) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_67,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3) = X6
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_52,c_0_38])]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_68,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk4_0) = k1_setfam_1(k2_tarski(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),X2) = k2_partfun1(esk4_0,esk2_0,esk6_0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_51]),c_0_58]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_48]),c_0_60])])).

cnf(c_0_71,negated_conjecture,
    ( k7_relat_1(esk5_0,esk3_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_72,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_64])).

cnf(c_0_73,negated_conjecture,
    ( k7_relat_1(esk6_0,esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_65]),c_0_59])])).

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
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( k7_relat_1(esk5_0,k1_setfam_1(k2_tarski(esk3_0,esk4_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_63])).

cnf(c_0_76,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),esk4_0) = X4
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk4_0))) != k2_partfun1(esk4_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk4_0)))
    | ~ v1_funct_2(X4,esk4_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_57])]),c_0_21])).

cnf(c_0_77,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),esk4_0) = k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_80,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),X2) = k2_partfun1(esk3_0,esk2_0,esk5_0,k1_setfam_1(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_63]),c_0_70]),c_0_70])).

cnf(c_0_81,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_71,c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_63]),c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),k1_setfam_1(k2_tarski(esk3_0,X2))) = k7_relat_1(k1_xboole_0,X2)
    | ~ v1_relat_1(k7_relat_1(X1,esk4_0))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,esk4_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_73,c_0_58])).

cnf(c_0_85,negated_conjecture,
    ( k7_relat_1(esk6_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_59]),c_0_73])).

cnf(c_0_86,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_2(X5,X2,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_74,c_0_38])]),c_0_53]),c_0_54]),c_0_55])).

cnf(c_0_87,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_setfam_1(k2_tarski(esk3_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_70])).

cnf(c_0_89,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_setfam_1(k2_tarski(esk3_0,esk4_0))) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_58])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),esk4_0) = esk6_0
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk2_0,X2,k1_setfam_1(k2_tarski(X1,esk4_0))) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))
    | ~ v1_funct_2(X2,X1,esk2_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_69]),c_0_77]),c_0_78]),c_0_44]),c_0_43])]),c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_70])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_70])).

cnf(c_0_93,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_setfam_1(k2_tarski(esk3_0,X1))) = k7_relat_1(k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_58]),c_0_84]),c_0_58]),c_0_84]),c_0_59]),c_0_59])])).

cnf(c_0_94,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_59]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_97,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk4_0))) != k2_partfun1(esk4_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk4_0)))
    | ~ v1_funct_2(X4,esk4_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_68]),c_0_57])]),c_0_21])).

cnf(c_0_98,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_68]),c_0_88]),c_0_68]),c_0_89])])).

cnf(c_0_99,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_92]),c_0_68]),c_0_93]),c_0_94]),c_0_95]),c_0_60]),c_0_48]),c_0_96])]),c_0_22])).

cnf(c_0_100,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),X1) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk2_0,X2,k1_setfam_1(k2_tarski(X1,esk4_0))) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))
    | ~ v1_funct_2(X2,X1,esk2_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_69]),c_0_77]),c_0_78]),c_0_44]),c_0_43])]),c_0_79])).

cnf(c_0_101,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_91]),c_0_92]),c_0_68]),c_0_93]),c_0_94]),c_0_95]),c_0_60]),c_0_48]),c_0_96])]),c_0_101]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:58:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 19.09/19.30  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 19.09/19.30  # and selection function SelectCQIPrecWNTNp.
% 19.09/19.30  #
% 19.09/19.30  # Preprocessing time       : 0.029 s
% 19.09/19.30  # Presaturation interreduction done
% 19.09/19.30  
% 19.09/19.30  # Proof found!
% 19.09/19.30  # SZS status Theorem
% 19.09/19.30  # SZS output start CNFRefutation
% 19.09/19.30  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 19.09/19.30  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 19.09/19.30  fof(symmetry_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)=>r1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 19.09/19.30  fof(t207_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_xboole_0(X1,X2)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 19.09/19.30  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 19.09/19.30  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 19.09/19.30  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 19.09/19.30  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 19.09/19.30  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.09/19.30  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 19.09/19.30  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 19.09/19.30  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 19.09/19.30  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 19.09/19.30  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 19.09/19.30  fof(c_0_14, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 19.09/19.30  fof(c_0_15, plain, ![X23, X24]:((~r1_subset_1(X23,X24)|r1_xboole_0(X23,X24)|(v1_xboole_0(X23)|v1_xboole_0(X24)))&(~r1_xboole_0(X23,X24)|r1_subset_1(X23,X24)|(v1_xboole_0(X23)|v1_xboole_0(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 19.09/19.30  fof(c_0_16, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)))&(r1_subset_1(esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 19.09/19.30  fof(c_0_17, plain, ![X25, X26]:(v1_xboole_0(X25)|v1_xboole_0(X26)|(~r1_subset_1(X25,X26)|r1_subset_1(X26,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).
% 19.09/19.30  fof(c_0_18, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|(~r1_xboole_0(X18,X19)|k7_relat_1(k7_relat_1(X20,X18),X19)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t207_relat_1])])).
% 19.09/19.30  cnf(c_0_19, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 19.09/19.30  cnf(c_0_20, negated_conjecture, (r1_subset_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_22, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  fof(c_0_23, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k7_relat_1(k7_relat_1(X17,X15),X16)=k7_relat_1(X17,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 19.09/19.30  fof(c_0_24, plain, ![X13, X14]:k1_setfam_1(k2_tarski(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 19.09/19.30  fof(c_0_25, plain, ![X44, X45, X46, X47, X48, X49]:(((v1_funct_1(k1_tmap_1(X44,X45,X46,X47,X48,X49))|(v1_xboole_0(X44)|v1_xboole_0(X45)|v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X44))|v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X44))|~v1_funct_1(X48)|~v1_funct_2(X48,X46,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))|~v1_funct_1(X49)|~v1_funct_2(X49,X47,X45)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))))&(v1_funct_2(k1_tmap_1(X44,X45,X46,X47,X48,X49),k4_subset_1(X44,X46,X47),X45)|(v1_xboole_0(X44)|v1_xboole_0(X45)|v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X44))|v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X44))|~v1_funct_1(X48)|~v1_funct_2(X48,X46,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))|~v1_funct_1(X49)|~v1_funct_2(X49,X47,X45)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45))))))&(m1_subset_1(k1_tmap_1(X44,X45,X46,X47,X48,X49),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X44,X46,X47),X45)))|(v1_xboole_0(X44)|v1_xboole_0(X45)|v1_xboole_0(X46)|~m1_subset_1(X46,k1_zfmisc_1(X44))|v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X44))|~v1_funct_1(X48)|~v1_funct_2(X48,X46,X45)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X45)))|~v1_funct_1(X49)|~v1_funct_2(X49,X47,X45)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 19.09/19.30  fof(c_0_26, plain, ![X11, X12]:(~v1_xboole_0(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 19.09/19.30  fof(c_0_27, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(X8))|k9_subset_1(X8,X9,X10)=k3_xboole_0(X9,X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 19.09/19.30  fof(c_0_28, plain, ![X33, X34, X35, X36]:(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_partfun1(X33,X34,X35,X36)=k7_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 19.09/19.30  fof(c_0_29, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 19.09/19.30  fof(c_0_30, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 19.09/19.30  cnf(c_0_31, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_subset_1(X2,X1)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 19.09/19.30  cnf(c_0_32, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 19.09/19.30  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22])).
% 19.09/19.30  cnf(c_0_34, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 19.09/19.30  cnf(c_0_35, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 19.09/19.30  fof(c_0_36, plain, ![X37, X38, X39, X40, X41, X42, X43]:(((k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X39)=X41|X43!=k1_tmap_1(X37,X38,X39,X40,X41,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,k4_subset_1(X37,X39,X40),X38)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X37,X39,X40),X38))))|k2_partfun1(X39,X38,X41,k9_subset_1(X37,X39,X40))!=k2_partfun1(X40,X38,X42,k9_subset_1(X37,X39,X40))|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X38)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X38))))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X38)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38))))|(v1_xboole_0(X40)|~m1_subset_1(X40,k1_zfmisc_1(X37)))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(X37)))|v1_xboole_0(X38)|v1_xboole_0(X37))&(k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X40)=X42|X43!=k1_tmap_1(X37,X38,X39,X40,X41,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,k4_subset_1(X37,X39,X40),X38)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X37,X39,X40),X38))))|k2_partfun1(X39,X38,X41,k9_subset_1(X37,X39,X40))!=k2_partfun1(X40,X38,X42,k9_subset_1(X37,X39,X40))|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X38)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X38))))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X38)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38))))|(v1_xboole_0(X40)|~m1_subset_1(X40,k1_zfmisc_1(X37)))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(X37)))|v1_xboole_0(X38)|v1_xboole_0(X37)))&(k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X39)!=X41|k2_partfun1(k4_subset_1(X37,X39,X40),X38,X43,X40)!=X42|X43=k1_tmap_1(X37,X38,X39,X40,X41,X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,k4_subset_1(X37,X39,X40),X38)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X37,X39,X40),X38))))|k2_partfun1(X39,X38,X41,k9_subset_1(X37,X39,X40))!=k2_partfun1(X40,X38,X42,k9_subset_1(X37,X39,X40))|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X38)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X38))))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X38)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X38))))|(v1_xboole_0(X40)|~m1_subset_1(X40,k1_zfmisc_1(X37)))|(v1_xboole_0(X39)|~m1_subset_1(X39,k1_zfmisc_1(X37)))|v1_xboole_0(X38)|v1_xboole_0(X37))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 19.09/19.30  cnf(c_0_37, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 19.09/19.30  cnf(c_0_38, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 19.09/19.30  cnf(c_0_39, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 19.09/19.30  cnf(c_0_40, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 19.09/19.30  cnf(c_0_41, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 19.09/19.30  cnf(c_0_42, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 19.09/19.30  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_45, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 19.09/19.30  fof(c_0_46, plain, ![X21, X22]:(~v1_relat_1(X22)|~v4_relat_1(X22,X21)|X22=k7_relat_1(X22,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 19.09/19.30  cnf(c_0_47, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 19.09/19.30  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_49, negated_conjecture, (r1_subset_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_20]), c_0_21]), c_0_22])).
% 19.09/19.30  cnf(c_0_50, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 19.09/19.30  cnf(c_0_51, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k1_setfam_1(k2_tarski(X2,X3)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 19.09/19.30  cnf(c_0_52, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 19.09/19.30  cnf(c_0_53, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 19.09/19.30  cnf(c_0_54, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_39, c_0_38])).
% 19.09/19.30  cnf(c_0_55, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_40, c_0_38])).
% 19.09/19.30  cnf(c_0_56, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_41, c_0_35])).
% 19.09/19.30  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_58, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 19.09/19.30  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_43])).
% 19.09/19.30  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_61, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 19.09/19.30  cnf(c_0_62, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 19.09/19.30  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_48])).
% 19.09/19.30  cnf(c_0_64, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_49]), c_0_22]), c_0_21])).
% 19.09/19.30  cnf(c_0_65, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_43])).
% 19.09/19.30  cnf(c_0_66, negated_conjecture, (k7_relat_1(X1,k1_setfam_1(k2_tarski(esk3_0,esk4_0)))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 19.09/19.30  cnf(c_0_67, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_52, c_0_38])]), c_0_53]), c_0_54]), c_0_55])).
% 19.09/19.30  cnf(c_0_68, negated_conjecture, (k9_subset_1(esk1_0,X1,esk4_0)=k1_setfam_1(k2_tarski(X1,esk4_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 19.09/19.30  cnf(c_0_69, negated_conjecture, (k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),X2)=k2_partfun1(esk4_0,esk2_0,esk6_0,k1_setfam_1(k2_tarski(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_51]), c_0_58]), c_0_59])])).
% 19.09/19.30  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_48]), c_0_60])])).
% 19.09/19.30  cnf(c_0_71, negated_conjecture, (k7_relat_1(esk5_0,esk3_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 19.09/19.30  cnf(c_0_72, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_32, c_0_64])).
% 19.09/19.30  cnf(c_0_73, negated_conjecture, (k7_relat_1(esk6_0,esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_65]), c_0_59])])).
% 19.09/19.30  cnf(c_0_74, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 19.09/19.30  cnf(c_0_75, negated_conjecture, (k7_relat_1(esk5_0,k1_setfam_1(k2_tarski(esk3_0,esk4_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_63])).
% 19.09/19.30  cnf(c_0_76, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),esk4_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk4_0)))!=k2_partfun1(esk4_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk4_0)))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_57])]), c_0_21])).
% 19.09/19.30  cnf(c_0_77, negated_conjecture, (k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),esk4_0)=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))), inference(spm,[status(thm)],[c_0_69, c_0_68])).
% 19.09/19.30  cnf(c_0_78, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_79, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_80, negated_conjecture, (k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),X2)=k2_partfun1(esk3_0,esk2_0,esk5_0,k1_setfam_1(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_63]), c_0_70]), c_0_70])).
% 19.09/19.30  cnf(c_0_81, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[c_0_71, c_0_70])).
% 19.09/19.30  cnf(c_0_82, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_63]), c_0_71])).
% 19.09/19.30  cnf(c_0_83, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),k1_setfam_1(k2_tarski(esk3_0,X2)))=k7_relat_1(k1_xboole_0,X2)|~v1_relat_1(k7_relat_1(X1,esk4_0))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_51, c_0_72])).
% 19.09/19.30  cnf(c_0_84, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,esk4_0)=esk6_0), inference(rw,[status(thm)],[c_0_73, c_0_58])).
% 19.09/19.30  cnf(c_0_85, negated_conjecture, (k7_relat_1(esk6_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_59]), c_0_73])).
% 19.09/19.30  cnf(c_0_86, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_74, c_0_38])]), c_0_53]), c_0_54]), c_0_55])).
% 19.09/19.30  cnf(c_0_87, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_88, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k1_setfam_1(k2_tarski(esk3_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[c_0_75, c_0_70])).
% 19.09/19.30  cnf(c_0_89, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k1_setfam_1(k2_tarski(esk3_0,esk4_0)))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_59]), c_0_58])).
% 19.09/19.30  cnf(c_0_90, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),esk4_0)=esk6_0|v1_xboole_0(X1)|k2_partfun1(X1,esk2_0,X2,k1_setfam_1(k2_tarski(X1,esk4_0)))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))|~v1_funct_2(X2,X1,esk2_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_69]), c_0_77]), c_0_78]), c_0_44]), c_0_43])]), c_0_79])).
% 19.09/19.30  cnf(c_0_91, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_70])).
% 19.09/19.30  cnf(c_0_92, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_70])).
% 19.09/19.30  cnf(c_0_93, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k1_setfam_1(k2_tarski(esk3_0,X1)))=k7_relat_1(k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_58]), c_0_84]), c_0_58]), c_0_84]), c_0_59]), c_0_59])])).
% 19.09/19.30  cnf(c_0_94, negated_conjecture, (k7_relat_1(k1_xboole_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_59]), c_0_85])).
% 19.09/19.30  cnf(c_0_95, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 19.09/19.30  cnf(c_0_97, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk4_0)))!=k2_partfun1(esk4_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk4_0)))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_68]), c_0_57])]), c_0_21])).
% 19.09/19.30  cnf(c_0_98, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_68]), c_0_88]), c_0_68]), c_0_89])])).
% 19.09/19.30  cnf(c_0_99, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_92]), c_0_68]), c_0_93]), c_0_94]), c_0_95]), c_0_60]), c_0_48]), c_0_96])]), c_0_22])).
% 19.09/19.30  cnf(c_0_100, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),X1)=X2|v1_xboole_0(X1)|k2_partfun1(X1,esk2_0,X2,k1_setfam_1(k2_tarski(X1,esk4_0)))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))|~v1_funct_2(X2,X1,esk2_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_69]), c_0_77]), c_0_78]), c_0_44]), c_0_43])]), c_0_79])).
% 19.09/19.30  cnf(c_0_101, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])])).
% 19.09/19.30  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_91]), c_0_92]), c_0_68]), c_0_93]), c_0_94]), c_0_95]), c_0_60]), c_0_48]), c_0_96])]), c_0_101]), c_0_22]), ['proof']).
% 19.09/19.30  # SZS output end CNFRefutation
% 19.09/19.30  # Proof object total steps             : 103
% 19.09/19.30  # Proof object clause steps            : 74
% 19.09/19.30  # Proof object formula steps           : 29
% 19.09/19.30  # Proof object conjectures             : 54
% 19.09/19.30  # Proof object clause conjectures      : 51
% 19.09/19.30  # Proof object formula conjectures     : 3
% 19.09/19.30  # Proof object initial clauses used    : 29
% 19.09/19.30  # Proof object initial formulas used   : 14
% 19.09/19.30  # Proof object generating inferences   : 32
% 19.09/19.30  # Proof object simplifying inferences  : 95
% 19.09/19.30  # Training examples: 0 positive, 0 negative
% 19.09/19.30  # Parsed axioms                        : 14
% 19.09/19.30  # Removed by relevancy pruning/SinE    : 0
% 19.09/19.30  # Initial clauses                      : 33
% 19.09/19.30  # Removed in clause preprocessing      : 1
% 19.09/19.30  # Initial clauses in saturation        : 32
% 19.09/19.30  # Processed clauses                    : 24800
% 19.09/19.30  # ...of these trivial                  : 168
% 19.09/19.30  # ...subsumed                          : 14265
% 19.09/19.30  # ...remaining for further processing  : 10367
% 19.09/19.30  # Other redundant clauses eliminated   : 4
% 19.09/19.30  # Clauses deleted for lack of memory   : 0
% 19.09/19.30  # Backward-subsumed                    : 41
% 19.09/19.30  # Backward-rewritten                   : 1078
% 19.09/19.30  # Generated clauses                    : 1022260
% 19.09/19.30  # ...of the previous two non-trivial   : 1021399
% 19.09/19.30  # Contextual simplify-reflections      : 12
% 19.09/19.30  # Paramodulations                      : 1022245
% 19.09/19.30  # Factorizations                       : 0
% 19.09/19.30  # Equation resolutions                 : 16
% 19.09/19.30  # Propositional unsat checks           : 0
% 19.09/19.30  #    Propositional check models        : 0
% 19.09/19.30  #    Propositional check unsatisfiable : 0
% 19.09/19.30  #    Propositional clauses             : 0
% 19.09/19.30  #    Propositional clauses after purity: 0
% 19.09/19.30  #    Propositional unsat core size     : 0
% 19.09/19.30  #    Propositional preprocessing time  : 0.000
% 19.09/19.30  #    Propositional encoding time       : 0.000
% 19.09/19.30  #    Propositional solver time         : 0.000
% 19.09/19.30  #    Success case prop preproc time    : 0.000
% 19.09/19.30  #    Success case prop encoding time   : 0.000
% 19.09/19.30  #    Success case prop solver time     : 0.000
% 19.09/19.30  # Current number of processed clauses  : 9213
% 19.09/19.30  #    Positive orientable unit clauses  : 4297
% 19.09/19.30  #    Positive unorientable unit clauses: 46
% 19.09/19.30  #    Negative unit clauses             : 5
% 19.09/19.30  #    Non-unit-clauses                  : 4865
% 19.09/19.30  # Current number of unprocessed clauses: 995407
% 19.09/19.30  # ...number of literals in the above   : 2824798
% 19.09/19.30  # Current number of archived formulas  : 0
% 19.09/19.30  # Current number of archived clauses   : 1152
% 19.09/19.30  # Clause-clause subsumption calls (NU) : 7461952
% 19.09/19.30  # Rec. Clause-clause subsumption calls : 5388401
% 19.09/19.30  # Non-unit clause-clause subsumptions  : 14239
% 19.09/19.30  # Unit Clause-clause subsumption calls : 208750
% 19.09/19.30  # Rewrite failures with RHS unbound    : 0
% 19.09/19.30  # BW rewrite match attempts            : 6053578
% 19.09/19.30  # BW rewrite match successes           : 4148
% 19.09/19.30  # Condensation attempts                : 0
% 19.09/19.30  # Condensation successes               : 0
% 19.09/19.30  # Termbank termtop insertions          : 58976087
% 19.09/19.35  
% 19.09/19.35  # -------------------------------------------------
% 19.09/19.35  # User time                : 18.504 s
% 19.09/19.35  # System time              : 0.506 s
% 19.09/19.35  # Total time               : 19.009 s
% 19.09/19.35  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
