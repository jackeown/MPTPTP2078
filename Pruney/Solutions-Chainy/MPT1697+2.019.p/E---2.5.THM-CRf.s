%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:38 EST 2020

% Result     : Theorem 18.27s
% Output     : CNFRefutation 18.27s
% Verified   : 
% Statistics : Number of formulae       :  111 (1905 expanded)
%              Number of clauses        :   78 ( 694 expanded)
%              Number of leaves         :   16 ( 469 expanded)
%              Depth                    :   13
%              Number of atoms          :  543 (16155 expanded)
%              Number of equality atoms :   96 (2941 expanded)
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

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

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

fof(symmetry_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
       => r1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(t100_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k7_relat_1(k7_relat_1(X3,X1),X2) = k7_relat_1(X3,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

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

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(X34)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | v1_xboole_0(X33) )
      & ( v1_partfun1(X34,X32)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_18,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( ( v4_relat_1(X31,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( v5_relat_1(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_20,plain,(
    ! [X26,X27,X28] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | v1_relat_1(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | v1_xboole_0(X25)
      | ~ r1_subset_1(X24,X25)
      | r1_subset_1(X25,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).

fof(c_0_22,plain,(
    ! [X35,X36] :
      ( ( ~ v1_partfun1(X36,X35)
        | k1_relat_1(X36) = X35
        | ~ v1_relat_1(X36)
        | ~ v4_relat_1(X36,X35) )
      & ( k1_relat_1(X36) != X35
        | v1_partfun1(X36,X35)
        | ~ v1_relat_1(X36)
        | ~ v4_relat_1(X36,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_23,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ( ~ r1_subset_1(X22,X23)
        | r1_xboole_0(X22,X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23) )
      & ( ~ r1_xboole_0(X22,X23)
        | r1_subset_1(X22,X23)
        | v1_xboole_0(X22)
        | v1_xboole_0(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_subset_1(X2,X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_35,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X18)
      | ~ r1_xboole_0(X19,k1_relat_1(X18))
      | k7_relat_1(X18,X19) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_36,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v1_partfun1(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_41,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( r1_subset_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])])).

fof(c_0_45,plain,(
    ! [X37,X38,X39,X40] :
      ( ~ v1_funct_1(X39)
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))
      | k2_partfun1(X37,X38,X39,X40) = k7_relat_1(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_49,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( ( v1_funct_1(k1_tmap_1(X48,X49,X50,X51,X52,X53))
        | v1_xboole_0(X48)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))) )
      & ( v1_funct_2(k1_tmap_1(X48,X49,X50,X51,X52,X53),k4_subset_1(X48,X50,X51),X49)
        | v1_xboole_0(X48)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))) )
      & ( m1_subset_1(k1_tmap_1(X48,X49,X50,X51,X52,X53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))
        | v1_xboole_0(X48)
        | v1_xboole_0(X49)
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_50,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_51,plain,(
    ! [X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ v4_relat_1(X21,X20)
      | X21 = k7_relat_1(X21,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

fof(c_0_52,plain,(
    ! [X15,X16,X17] :
      ( ~ v1_relat_1(X17)
      | k7_relat_1(k7_relat_1(X17,X15),X16) = k7_relat_1(X17,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

cnf(c_0_53,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_34]),c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_39])])).

cnf(c_0_56,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_46]),c_0_47]),c_0_48])]),c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_48])).

fof(c_0_60,plain,(
    ! [X41,X42,X43,X44,X45,X46,X47] :
      ( ( k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43) = X45
        | X47 != k1_tmap_1(X41,X42,X43,X44,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42)))
        | k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44)) != k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X41))
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) )
      & ( k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44) = X46
        | X47 != k1_tmap_1(X41,X42,X43,X44,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42)))
        | k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44)) != k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X41))
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) )
      & ( k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43) != X45
        | k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44) != X46
        | X47 = k1_tmap_1(X41,X42,X43,X44,X45,X46)
        | ~ v1_funct_1(X47)
        | ~ v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42)))
        | k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44)) != k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X44,X42)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42)))
        | v1_xboole_0(X44)
        | ~ m1_subset_1(X44,k1_zfmisc_1(X41))
        | v1_xboole_0(X43)
        | ~ m1_subset_1(X43,k1_zfmisc_1(X41))
        | v1_xboole_0(X42)
        | v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_63,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_65,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_66,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_67,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_68,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_54])).

cnf(c_0_71,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_26]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_57]),c_0_58]),c_0_59])])).

cnf(c_0_73,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_47])])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,plain,
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
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_76,plain,
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
    inference(csr,[status(thm)],[c_0_63,c_0_62])).

cnf(c_0_77,plain,
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
    inference(csr,[status(thm)],[c_0_64,c_0_62])).

cnf(c_0_78,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_80,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( k7_relat_1(esk5_0,esk3_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_38]),c_0_39])])).

cnf(c_0_82,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0) = k7_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_83,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( k7_relat_1(esk6_0,esk4_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_58]),c_0_59])])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_72]),c_0_59])]),c_0_73])).

cnf(c_0_86,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_74,c_0_62])]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk4_0) = k3_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_88,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),X2) = k2_partfun1(esk4_0,esk2_0,esk6_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_68]),c_0_73]),c_0_59])])).

cnf(c_0_89,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_90,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0) = k7_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_68,c_0_80])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk3_0) = esk5_0 ),
    inference(rw,[status(thm)],[c_0_81,c_0_71])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) = k7_relat_1(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_71]),c_0_83]),c_0_71]),c_0_39])])).

cnf(c_0_93,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,esk4_0) = esk6_0 ),
    inference(rw,[status(thm)],[c_0_84,c_0_73])).

cnf(c_0_94,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_85,c_0_66])).

cnf(c_0_95,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_79])]),c_0_33])).

cnf(c_0_96,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),esk4_0) = k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_97,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),X2) = k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_71]),c_0_71]),c_0_39])])).

cnf(c_0_98,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_89,c_0_62])]),c_0_75]),c_0_76]),c_0_77])).

cnf(c_0_99,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_100,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_71]),c_0_91]),c_0_71]),c_0_83]),c_0_71]),c_0_92]),c_0_39])])).

cnf(c_0_101,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_73]),c_0_93]),c_0_73]),c_0_94]),c_0_73]),c_0_59])])).

cnf(c_0_102,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),esk4_0) = esk6_0
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk2_0,X2,k3_xboole_0(X1,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))
    | ~ v1_funct_2(X2,X1,esk2_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_88]),c_0_96]),c_0_46]),c_0_47]),c_0_48])]),c_0_27])).

cnf(c_0_103,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(esk3_0,X1)) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_91]),c_0_71])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_105,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_87]),c_0_79])]),c_0_33])).

cnf(c_0_106,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_87]),c_0_80]),c_0_92]),c_0_100]),c_0_87]),c_0_80]),c_0_101])])).

cnf(c_0_107,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_83]),c_0_87]),c_0_80]),c_0_101]),c_0_24]),c_0_25]),c_0_26]),c_0_104])]),c_0_34])).

cnf(c_0_108,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),X1) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk2_0,X2,k3_xboole_0(X1,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))
    | ~ v1_funct_2(X2,X1,esk2_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_88]),c_0_96]),c_0_46]),c_0_47]),c_0_48])]),c_0_27])).

cnf(c_0_109,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106,c_0_107])])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_103]),c_0_83]),c_0_87]),c_0_80]),c_0_101]),c_0_24]),c_0_25]),c_0_26]),c_0_104])]),c_0_109]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 18.27/18.44  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 18.27/18.44  # and selection function SelectCQIPrecWNTNp.
% 18.27/18.44  #
% 18.27/18.44  # Preprocessing time       : 0.030 s
% 18.27/18.44  # Presaturation interreduction done
% 18.27/18.44  
% 18.27/18.44  # Proof found!
% 18.27/18.44  # SZS status Theorem
% 18.27/18.44  # SZS output start CNFRefutation
% 18.27/18.44  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 18.27/18.44  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 18.27/18.44  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.27/18.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.27/18.44  fof(symmetry_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)=>r1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 18.27/18.44  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 18.27/18.44  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 18.27/18.44  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 18.27/18.44  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 18.27/18.44  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 18.27/18.44  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 18.27/18.44  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 18.27/18.44  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 18.27/18.44  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 18.27/18.44  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 18.27/18.44  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 18.27/18.44  fof(c_0_16, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 18.27/18.44  fof(c_0_17, plain, ![X32, X33, X34]:((v1_funct_1(X34)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_xboole_0(X33))&(v1_partfun1(X34,X32)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|v1_xboole_0(X33))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 18.27/18.44  fof(c_0_18, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)))&(r1_subset_1(esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 18.27/18.44  fof(c_0_19, plain, ![X29, X30, X31]:((v4_relat_1(X31,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))&(v5_relat_1(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 18.27/18.44  fof(c_0_20, plain, ![X26, X27, X28]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|v1_relat_1(X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 18.27/18.44  fof(c_0_21, plain, ![X24, X25]:(v1_xboole_0(X24)|v1_xboole_0(X25)|(~r1_subset_1(X24,X25)|r1_subset_1(X25,X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).
% 18.27/18.44  fof(c_0_22, plain, ![X35, X36]:((~v1_partfun1(X36,X35)|k1_relat_1(X36)=X35|(~v1_relat_1(X36)|~v4_relat_1(X36,X35)))&(k1_relat_1(X36)!=X35|v1_partfun1(X36,X35)|(~v1_relat_1(X36)|~v4_relat_1(X36,X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 18.27/18.44  cnf(c_0_23, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 18.27/18.44  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_27, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_28, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 18.27/18.44  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 18.27/18.44  fof(c_0_30, plain, ![X22, X23]:((~r1_subset_1(X22,X23)|r1_xboole_0(X22,X23)|(v1_xboole_0(X22)|v1_xboole_0(X23)))&(~r1_xboole_0(X22,X23)|r1_subset_1(X22,X23)|(v1_xboole_0(X22)|v1_xboole_0(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 18.27/18.44  cnf(c_0_31, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_subset_1(X2,X1)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 18.27/18.44  cnf(c_0_32, negated_conjecture, (r1_subset_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_34, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  fof(c_0_35, plain, ![X18, X19]:(~v1_relat_1(X18)|(~r1_xboole_0(X19,k1_relat_1(X18))|k7_relat_1(X18,X19)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 18.27/18.44  cnf(c_0_36, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 18.27/18.44  cnf(c_0_37, negated_conjecture, (v1_partfun1(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27])).
% 18.27/18.44  cnf(c_0_38, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 18.27/18.44  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 18.27/18.44  fof(c_0_40, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 18.27/18.44  cnf(c_0_41, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 18.27/18.44  cnf(c_0_42, negated_conjecture, (r1_subset_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 18.27/18.44  cnf(c_0_43, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 18.27/18.44  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])])).
% 18.27/18.44  fof(c_0_45, plain, ![X37, X38, X39, X40]:(~v1_funct_1(X39)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))|k2_partfun1(X37,X38,X39,X40)=k7_relat_1(X39,X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 18.27/18.44  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_47, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  fof(c_0_49, plain, ![X48, X49, X50, X51, X52, X53]:(((v1_funct_1(k1_tmap_1(X48,X49,X50,X51,X52,X53))|(v1_xboole_0(X48)|v1_xboole_0(X49)|v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48))|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48))|~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))))&(v1_funct_2(k1_tmap_1(X48,X49,X50,X51,X52,X53),k4_subset_1(X48,X50,X51),X49)|(v1_xboole_0(X48)|v1_xboole_0(X49)|v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48))|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48))|~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))))))&(m1_subset_1(k1_tmap_1(X48,X49,X50,X51,X52,X53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))|(v1_xboole_0(X48)|v1_xboole_0(X49)|v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48))|v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48))|~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 18.27/18.44  fof(c_0_50, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 18.27/18.44  fof(c_0_51, plain, ![X20, X21]:(~v1_relat_1(X21)|~v4_relat_1(X21,X20)|X21=k7_relat_1(X21,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 18.27/18.44  fof(c_0_52, plain, ![X15, X16, X17]:(~v1_relat_1(X17)|k7_relat_1(k7_relat_1(X17,X15),X16)=k7_relat_1(X17,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 18.27/18.44  cnf(c_0_53, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 18.27/18.44  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_34]), c_0_33])).
% 18.27/18.44  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk5_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_39])])).
% 18.27/18.44  cnf(c_0_56, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 18.27/18.44  cnf(c_0_57, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_46]), c_0_47]), c_0_48])]), c_0_27])).
% 18.27/18.44  cnf(c_0_58, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 18.27/18.44  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_48])).
% 18.27/18.44  fof(c_0_60, plain, ![X41, X42, X43, X44, X45, X46, X47]:(((k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43)=X45|X47!=k1_tmap_1(X41,X42,X43,X44,X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42))))|k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44))!=k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X42)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42))))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X42)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X41)))|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(X41)))|v1_xboole_0(X42)|v1_xboole_0(X41))&(k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44)=X46|X47!=k1_tmap_1(X41,X42,X43,X44,X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42))))|k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44))!=k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X42)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42))))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X42)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X41)))|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(X41)))|v1_xboole_0(X42)|v1_xboole_0(X41)))&(k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X43)!=X45|k2_partfun1(k4_subset_1(X41,X43,X44),X42,X47,X44)!=X46|X47=k1_tmap_1(X41,X42,X43,X44,X45,X46)|(~v1_funct_1(X47)|~v1_funct_2(X47,k4_subset_1(X41,X43,X44),X42)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X41,X43,X44),X42))))|k2_partfun1(X43,X42,X45,k9_subset_1(X41,X43,X44))!=k2_partfun1(X44,X42,X46,k9_subset_1(X41,X43,X44))|(~v1_funct_1(X46)|~v1_funct_2(X46,X44,X42)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X42))))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X42)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X42))))|(v1_xboole_0(X44)|~m1_subset_1(X44,k1_zfmisc_1(X41)))|(v1_xboole_0(X43)|~m1_subset_1(X43,k1_zfmisc_1(X41)))|v1_xboole_0(X42)|v1_xboole_0(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 18.27/18.44  cnf(c_0_61, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 18.27/18.44  cnf(c_0_62, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 18.27/18.44  cnf(c_0_63, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 18.27/18.44  cnf(c_0_64, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 18.27/18.44  fof(c_0_65, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 18.27/18.44  cnf(c_0_66, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_32]), c_0_33]), c_0_34])).
% 18.27/18.44  cnf(c_0_67, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 18.27/18.44  cnf(c_0_68, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 18.27/18.44  cnf(c_0_69, negated_conjecture, (k3_xboole_0(esk4_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 18.27/18.44  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_54])).
% 18.27/18.44  cnf(c_0_71, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_26]), c_0_25])])).
% 18.27/18.44  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_57]), c_0_58]), c_0_59])])).
% 18.27/18.44  cnf(c_0_73, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_47])])).
% 18.27/18.44  cnf(c_0_74, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 18.27/18.44  cnf(c_0_75, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 18.27/18.44  cnf(c_0_76, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_63, c_0_62])).
% 18.27/18.44  cnf(c_0_77, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_64, c_0_62])).
% 18.27/18.44  cnf(c_0_78, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 18.27/18.44  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.44  cnf(c_0_80, negated_conjecture, (k3_xboole_0(esk3_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_66])).
% 18.27/18.44  cnf(c_0_81, negated_conjecture, (k7_relat_1(esk5_0,esk3_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_38]), c_0_39])])).
% 18.27/18.44  cnf(c_0_82, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),esk3_0)=k7_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 18.27/18.44  cnf(c_0_83, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_70, c_0_71])).
% 18.27/18.44  cnf(c_0_84, negated_conjecture, (k7_relat_1(esk6_0,esk4_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_58]), c_0_59])])).
% 18.27/18.44  cnf(c_0_85, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_72]), c_0_59])]), c_0_73])).
% 18.27/18.44  cnf(c_0_86, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_74, c_0_62])]), c_0_75]), c_0_76]), c_0_77])).
% 18.27/18.44  cnf(c_0_87, negated_conjecture, (k9_subset_1(esk1_0,X1,esk4_0)=k3_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 18.27/18.44  cnf(c_0_88, negated_conjecture, (k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),X2)=k2_partfun1(esk4_0,esk2_0,esk6_0,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_68]), c_0_73]), c_0_59])])).
% 18.27/18.44  cnf(c_0_89, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 18.27/18.44  cnf(c_0_90, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk3_0),esk4_0)=k7_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_68, c_0_80])).
% 18.27/18.44  cnf(c_0_91, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk3_0)=esk5_0), inference(rw,[status(thm)],[c_0_81, c_0_71])).
% 18.27/18.44  cnf(c_0_92, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0)=k7_relat_1(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_71]), c_0_83]), c_0_71]), c_0_39])])).
% 18.27/18.44  cnf(c_0_93, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,esk4_0)=esk6_0), inference(rw,[status(thm)],[c_0_84, c_0_73])).
% 18.27/18.44  cnf(c_0_94, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_85, c_0_66])).
% 18.27/18.44  cnf(c_0_95, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),esk4_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk4_0))!=k2_partfun1(esk4_0,X2,X4,k3_xboole_0(X1,esk4_0))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_79])]), c_0_33])).
% 18.27/18.44  cnf(c_0_96, negated_conjecture, (k7_relat_1(k2_partfun1(esk4_0,esk2_0,esk6_0,X1),esk4_0)=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))), inference(spm,[status(thm)],[c_0_88, c_0_87])).
% 18.27/18.44  cnf(c_0_97, negated_conjecture, (k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),X2)=k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_71]), c_0_71]), c_0_39])])).
% 18.27/18.44  cnf(c_0_98, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_89, c_0_62])]), c_0_75]), c_0_76]), c_0_77])).
% 18.27/18.45  cnf(c_0_99, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.45  cnf(c_0_100, negated_conjecture, (k7_relat_1(k1_xboole_0,esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_71]), c_0_91]), c_0_71]), c_0_83]), c_0_71]), c_0_92]), c_0_39])])).
% 18.27/18.45  cnf(c_0_101, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_73]), c_0_93]), c_0_73]), c_0_94]), c_0_73]), c_0_59])])).
% 18.27/18.45  cnf(c_0_102, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),esk4_0)=esk6_0|v1_xboole_0(X1)|k2_partfun1(X1,esk2_0,X2,k3_xboole_0(X1,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))|~v1_funct_2(X2,X1,esk2_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_88]), c_0_96]), c_0_46]), c_0_47]), c_0_48])]), c_0_27])).
% 18.27/18.45  cnf(c_0_103, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(esk3_0,X1))=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_91]), c_0_71])).
% 18.27/18.45  cnf(c_0_104, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 18.27/18.45  cnf(c_0_105, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k3_xboole_0(X1,esk4_0))!=k2_partfun1(esk4_0,X2,X4,k3_xboole_0(X1,esk4_0))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_87]), c_0_79])]), c_0_33])).
% 18.27/18.45  cnf(c_0_106, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_99, c_0_87]), c_0_80]), c_0_92]), c_0_100]), c_0_87]), c_0_80]), c_0_101])])).
% 18.27/18.45  cnf(c_0_107, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_83]), c_0_87]), c_0_80]), c_0_101]), c_0_24]), c_0_25]), c_0_26]), c_0_104])]), c_0_34])).
% 18.27/18.45  cnf(c_0_108, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),X1)=X2|v1_xboole_0(X1)|k2_partfun1(X1,esk2_0,X2,k3_xboole_0(X1,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))|~v1_funct_2(X2,X1,esk2_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_88]), c_0_96]), c_0_46]), c_0_47]), c_0_48])]), c_0_27])).
% 18.27/18.45  cnf(c_0_109, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_106, c_0_107])])).
% 18.27/18.45  cnf(c_0_110, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_103]), c_0_83]), c_0_87]), c_0_80]), c_0_101]), c_0_24]), c_0_25]), c_0_26]), c_0_104])]), c_0_109]), c_0_34]), ['proof']).
% 18.27/18.45  # SZS output end CNFRefutation
% 18.27/18.45  # Proof object total steps             : 111
% 18.27/18.45  # Proof object clause steps            : 78
% 18.27/18.45  # Proof object formula steps           : 33
% 18.27/18.45  # Proof object conjectures             : 58
% 18.27/18.45  # Proof object clause conjectures      : 55
% 18.27/18.45  # Proof object formula conjectures     : 3
% 18.27/18.45  # Proof object initial clauses used    : 31
% 18.27/18.45  # Proof object initial formulas used   : 16
% 18.27/18.45  # Proof object generating inferences   : 37
% 18.27/18.45  # Proof object simplifying inferences  : 122
% 18.27/18.45  # Training examples: 0 positive, 0 negative
% 18.27/18.45  # Parsed axioms                        : 16
% 18.27/18.45  # Removed by relevancy pruning/SinE    : 0
% 18.27/18.45  # Initial clauses                      : 38
% 18.27/18.45  # Removed in clause preprocessing      : 1
% 18.27/18.45  # Initial clauses in saturation        : 37
% 18.27/18.45  # Processed clauses                    : 16638
% 18.27/18.45  # ...of these trivial                  : 229
% 18.27/18.45  # ...subsumed                          : 6848
% 18.27/18.45  # ...remaining for further processing  : 9561
% 18.27/18.45  # Other redundant clauses eliminated   : 5
% 18.27/18.45  # Clauses deleted for lack of memory   : 0
% 18.27/18.45  # Backward-subsumed                    : 16
% 18.27/18.45  # Backward-rewritten                   : 504
% 18.27/18.45  # Generated clauses                    : 852256
% 18.27/18.45  # ...of the previous two non-trivial   : 851551
% 18.27/18.45  # Contextual simplify-reflections      : 12
% 18.27/18.45  # Paramodulations                      : 852240
% 18.27/18.45  # Factorizations                       : 0
% 18.27/18.45  # Equation resolutions                 : 17
% 18.27/18.45  # Propositional unsat checks           : 0
% 18.27/18.45  #    Propositional check models        : 0
% 18.27/18.45  #    Propositional check unsatisfiable : 0
% 18.27/18.45  #    Propositional clauses             : 0
% 18.27/18.45  #    Propositional clauses after purity: 0
% 18.27/18.45  #    Propositional unsat core size     : 0
% 18.27/18.45  #    Propositional preprocessing time  : 0.000
% 18.27/18.45  #    Propositional encoding time       : 0.000
% 18.27/18.45  #    Propositional solver time         : 0.000
% 18.27/18.45  #    Success case prop preproc time    : 0.000
% 18.27/18.45  #    Success case prop encoding time   : 0.000
% 18.27/18.45  #    Success case prop solver time     : 0.000
% 18.27/18.45  # Current number of processed clauses  : 9000
% 18.27/18.45  #    Positive orientable unit clauses  : 4920
% 18.27/18.45  #    Positive unorientable unit clauses: 62
% 18.27/18.45  #    Negative unit clauses             : 5
% 18.27/18.45  #    Non-unit-clauses                  : 4013
% 18.27/18.45  # Current number of unprocessed clauses: 834326
% 18.27/18.45  # ...number of literals in the above   : 2466169
% 18.27/18.45  # Current number of archived formulas  : 0
% 18.27/18.45  # Current number of archived clauses   : 557
% 18.27/18.45  # Clause-clause subsumption calls (NU) : 2152826
% 18.27/18.45  # Rec. Clause-clause subsumption calls : 1760774
% 18.27/18.45  # Non-unit clause-clause subsumptions  : 6728
% 18.27/18.45  # Unit Clause-clause subsumption calls : 147563
% 18.27/18.45  # Rewrite failures with RHS unbound    : 0
% 18.27/18.45  # BW rewrite match attempts            : 12934963
% 18.27/18.45  # BW rewrite match successes           : 1383
% 18.27/18.45  # Condensation attempts                : 0
% 18.27/18.45  # Condensation successes               : 0
% 18.27/18.45  # Termbank termtop insertions          : 63877574
% 18.32/18.49  
% 18.32/18.49  # -------------------------------------------------
% 18.32/18.49  # User time                : 17.678 s
% 18.32/18.49  # System time              : 0.473 s
% 18.32/18.49  # Total time               : 18.151 s
% 18.32/18.49  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
