%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:41 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  103 (1538 expanded)
%              Number of clauses        :   72 ( 561 expanded)
%              Number of leaves         :   15 ( 377 expanded)
%              Depth                    :   13
%              Number of atoms          :  468 (13211 expanded)
%              Number of equality atoms :   90 (2392 expanded)
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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(t192_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,X1) = k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(symmetry_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
       => r1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_subset_1)).

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X30,X31,X32] :
      ( ( v1_funct_1(X32)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | v1_xboole_0(X31) )
      & ( v1_partfun1(X32,X30)
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_17,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_18,plain,(
    ! [X27,X28,X29] :
      ( ( v4_relat_1(X29,X27)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( v5_relat_1(X29,X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | v1_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( ( ~ v1_partfun1(X34,X33)
        | k1_relat_1(X34) = X33
        | ~ v1_relat_1(X34)
        | ~ v4_relat_1(X34,X33) )
      & ( k1_relat_1(X34) != X33
        | v1_partfun1(X34,X33)
        | ~ v1_relat_1(X34)
        | ~ v4_relat_1(X34,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_21,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_31,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | k7_relat_1(X19,X18) = k7_relat_1(X19,k3_xboole_0(k1_relat_1(X19),X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_32,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_24])).

fof(c_0_36,plain,(
    ! [X35,X36,X37,X38] :
      ( ~ v1_funct_1(X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | k2_partfun1(X35,X36,X37,X38) = k7_relat_1(X37,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( v1_xboole_0(X22)
      | v1_xboole_0(X23)
      | ~ r1_subset_1(X22,X23)
      | r1_subset_1(X23,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).

cnf(c_0_38,negated_conjecture,
    ( v1_partfun1(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_28]),c_0_29]),c_0_30])]),c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_30])).

cnf(c_0_41,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])])).

cnf(c_0_43,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_44,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | ~ r1_xboole_0(X17,k1_relat_1(X16))
      | k7_relat_1(X16,X17) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

fof(c_0_45,plain,(
    ! [X20,X21] :
      ( ( ~ r1_subset_1(X20,X21)
        | r1_xboole_0(X20,X21)
        | v1_xboole_0(X20)
        | v1_xboole_0(X21) )
      & ( ~ r1_xboole_0(X20,X21)
        | r1_subset_1(X20,X21)
        | v1_xboole_0(X20)
        | v1_xboole_0(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | r1_subset_1(X2,X1)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_38]),c_0_39]),c_0_40])])).

fof(c_0_51,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_52,negated_conjecture,
    ( k7_relat_1(esk6_0,k3_xboole_0(esk4_0,X1)) = k7_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35])])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_24]),c_0_23])])).

fof(c_0_54,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_55,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( r1_subset_1(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k7_relat_1(esk5_0,k3_xboole_0(esk3_0,X1)) = k7_relat_1(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_50]),c_0_40])])).

cnf(c_0_59,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_60,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X15)
      | k7_relat_1(k7_relat_1(X15,X13),X14) = k7_relat_1(X15,k3_xboole_0(X13,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).

fof(c_0_61,plain,(
    ! [X39,X40,X41,X42,X43,X44,X45] :
      ( ( k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41) = X43
        | X45 != k1_tmap_1(X39,X40,X41,X42,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40)))
        | k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42)) != k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X40)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X39))
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | v1_xboole_0(X40)
        | v1_xboole_0(X39) )
      & ( k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42) = X44
        | X45 != k1_tmap_1(X39,X40,X41,X42,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40)))
        | k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42)) != k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X40)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X39))
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | v1_xboole_0(X40)
        | v1_xboole_0(X39) )
      & ( k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41) != X43
        | k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42) != X44
        | X45 = k1_tmap_1(X39,X40,X41,X42,X43,X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40)))
        | k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42)) != k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X42,X40)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40)))
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X41,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40)))
        | v1_xboole_0(X42)
        | ~ m1_subset_1(X42,k1_zfmisc_1(X39))
        | v1_xboole_0(X41)
        | ~ m1_subset_1(X41,k1_zfmisc_1(X39))
        | v1_xboole_0(X40)
        | v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_62,plain,(
    ! [X46,X47,X48,X49,X50,X51] :
      ( ( v1_funct_1(k1_tmap_1(X46,X47,X48,X49,X50,X51))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47)
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X46))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X47)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))) )
      & ( v1_funct_2(k1_tmap_1(X46,X47,X48,X49,X50,X51),k4_subset_1(X46,X48,X49),X47)
        | v1_xboole_0(X46)
        | v1_xboole_0(X47)
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X46))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X47)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))) )
      & ( m1_subset_1(k1_tmap_1(X46,X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X46,X48,X49),X47)))
        | v1_xboole_0(X46)
        | v1_xboole_0(X47)
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X46))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X46))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X47)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

cnf(c_0_63,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k3_xboole_0(esk4_0,X1)) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53])).

cnf(c_0_64,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_66,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_50]),c_0_40])])).

cnf(c_0_67,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_49]),c_0_48])).

cnf(c_0_68,negated_conjecture,
    ( k7_relat_1(esk5_0,k3_xboole_0(X1,esk3_0)) = k7_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_29])])).

cnf(c_0_70,plain,
    ( k7_relat_1(k7_relat_1(X1,X2),X3) = k7_relat_1(X1,k3_xboole_0(X2,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_35])])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_77,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k3_xboole_0(X1,esk4_0)) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

cnf(c_0_78,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk4_0) = k3_xboole_0(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_79,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(X1,esk3_0)) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69]),c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),X2) = k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_40]),c_0_69]),c_0_69])).

cnf(c_0_82,negated_conjecture,
    ( k7_relat_1(esk6_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_83,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0)) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_86,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk4_0) = k3_xboole_0(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_79,c_0_69])).

cnf(c_0_88,negated_conjecture,
    ( k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),esk3_0) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_81])).

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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_90,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(esk3_0,X1)) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_69]),c_0_69])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_82,c_0_53])).

cnf(c_0_93,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),esk4_0) = esk6_0
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk2_0,X2,k9_subset_1(esk1_0,X1,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,X1)
    | ~ v1_funct_2(X2,X1,esk2_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_22]),c_0_23]),c_0_24]),c_0_65])]),c_0_85]),c_0_48]),c_0_25])).

cnf(c_0_94,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,X1) = k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,X1,esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_86]),c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_87])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_97,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]),c_0_74]),c_0_75]),c_0_76])).

cnf(c_0_98,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_78]),c_0_78]),c_0_91]),c_0_87]),c_0_77]),c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95]),c_0_92]),c_0_28]),c_0_29]),c_0_30]),c_0_96])]),c_0_49])).

cnf(c_0_100,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),X1) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(X1,esk2_0,X2,k9_subset_1(esk1_0,X1,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,X1)
    | ~ v1_funct_2(X2,X1,esk2_0)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_84]),c_0_22]),c_0_23]),c_0_24]),c_0_65])]),c_0_85]),c_0_48]),c_0_25])).

cnf(c_0_101,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_99])])).

cnf(c_0_102,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_94]),c_0_95]),c_0_92]),c_0_28]),c_0_29]),c_0_30]),c_0_96])]),c_0_101]),c_0_49]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:18:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.49  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.49  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.49  #
% 0.18/0.49  # Preprocessing time       : 0.029 s
% 0.18/0.49  # Presaturation interreduction done
% 0.18/0.49  
% 0.18/0.49  # Proof found!
% 0.18/0.49  # SZS status Theorem
% 0.18/0.49  # SZS output start CNFRefutation
% 0.18/0.49  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.18/0.49  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.18/0.49  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.49  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.49  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.18/0.49  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.18/0.49  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.18/0.49  fof(symmetry_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)=>r1_subset_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_subset_1)).
% 0.18/0.49  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.18/0.49  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.18/0.49  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.18/0.49  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.18/0.49  fof(t100_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k7_relat_1(k7_relat_1(X3,X1),X2)=k7_relat_1(X3,k3_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 0.18/0.49  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.18/0.49  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.18/0.49  fof(c_0_15, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.18/0.49  fof(c_0_16, plain, ![X30, X31, X32]:((v1_funct_1(X32)|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_xboole_0(X31))&(v1_partfun1(X32,X30)|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_xboole_0(X31))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.18/0.49  fof(c_0_17, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)))&(r1_subset_1(esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.18/0.49  fof(c_0_18, plain, ![X27, X28, X29]:((v4_relat_1(X29,X27)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))&(v5_relat_1(X29,X28)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.49  fof(c_0_19, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|v1_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.49  fof(c_0_20, plain, ![X33, X34]:((~v1_partfun1(X34,X33)|k1_relat_1(X34)=X33|(~v1_relat_1(X34)|~v4_relat_1(X34,X33)))&(k1_relat_1(X34)!=X33|v1_partfun1(X34,X33)|(~v1_relat_1(X34)|~v4_relat_1(X34,X33)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.18/0.49  cnf(c_0_21, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.49  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_25, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_26, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.49  cnf(c_0_27, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.49  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  fof(c_0_31, plain, ![X18, X19]:(~v1_relat_1(X19)|k7_relat_1(X19,X18)=k7_relat_1(X19,k3_xboole_0(k1_relat_1(X19),X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.18/0.49  cnf(c_0_32, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.49  cnf(c_0_33, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.18/0.49  cnf(c_0_34, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.18/0.49  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_27, c_0_24])).
% 0.18/0.49  fof(c_0_36, plain, ![X35, X36, X37, X38]:(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|k2_partfun1(X35,X36,X37,X38)=k7_relat_1(X37,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.18/0.49  fof(c_0_37, plain, ![X22, X23]:(v1_xboole_0(X22)|v1_xboole_0(X23)|(~r1_subset_1(X22,X23)|r1_subset_1(X23,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[symmetry_r1_subset_1])])])).
% 0.18/0.49  cnf(c_0_38, negated_conjecture, (v1_partfun1(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_28]), c_0_29]), c_0_30])]), c_0_25])).
% 0.18/0.49  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_30])).
% 0.18/0.49  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_30])).
% 0.18/0.49  cnf(c_0_41, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.18/0.49  cnf(c_0_42, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])])).
% 0.18/0.49  cnf(c_0_43, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.18/0.49  fof(c_0_44, plain, ![X16, X17]:(~v1_relat_1(X16)|(~r1_xboole_0(X17,k1_relat_1(X16))|k7_relat_1(X16,X17)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.18/0.49  fof(c_0_45, plain, ![X20, X21]:((~r1_subset_1(X20,X21)|r1_xboole_0(X20,X21)|(v1_xboole_0(X20)|v1_xboole_0(X21)))&(~r1_xboole_0(X20,X21)|r1_subset_1(X20,X21)|(v1_xboole_0(X20)|v1_xboole_0(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.18/0.49  cnf(c_0_46, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|r1_subset_1(X2,X1)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.18/0.49  cnf(c_0_47, negated_conjecture, (r1_subset_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_49, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_38]), c_0_39]), c_0_40])])).
% 0.18/0.49  fof(c_0_51, plain, ![X8, X9]:k3_xboole_0(X8,X9)=k3_xboole_0(X9,X8), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.18/0.49  cnf(c_0_52, negated_conjecture, (k7_relat_1(esk6_0,k3_xboole_0(esk4_0,X1))=k7_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_35])])).
% 0.18/0.49  cnf(c_0_53, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_24]), c_0_23])])).
% 0.18/0.49  fof(c_0_54, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.18/0.49  cnf(c_0_55, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.18/0.49  cnf(c_0_56, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.49  cnf(c_0_57, negated_conjecture, (r1_subset_1(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 0.18/0.49  cnf(c_0_58, negated_conjecture, (k7_relat_1(esk5_0,k3_xboole_0(esk3_0,X1))=k7_relat_1(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_50]), c_0_40])])).
% 0.18/0.49  cnf(c_0_59, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.18/0.49  fof(c_0_60, plain, ![X13, X14, X15]:(~v1_relat_1(X15)|k7_relat_1(k7_relat_1(X15,X13),X14)=k7_relat_1(X15,k3_xboole_0(X13,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t100_relat_1])])).
% 0.18/0.49  fof(c_0_61, plain, ![X39, X40, X41, X42, X43, X44, X45]:(((k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41)=X43|X45!=k1_tmap_1(X39,X40,X41,X42,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40))))|k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42))!=k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X40)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40))))|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(X39)))|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39)))|v1_xboole_0(X40)|v1_xboole_0(X39))&(k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42)=X44|X45!=k1_tmap_1(X39,X40,X41,X42,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40))))|k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42))!=k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X40)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40))))|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(X39)))|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39)))|v1_xboole_0(X40)|v1_xboole_0(X39)))&(k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X41)!=X43|k2_partfun1(k4_subset_1(X39,X41,X42),X40,X45,X42)!=X44|X45=k1_tmap_1(X39,X40,X41,X42,X43,X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,k4_subset_1(X39,X41,X42),X40)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X39,X41,X42),X40))))|k2_partfun1(X41,X40,X43,k9_subset_1(X39,X41,X42))!=k2_partfun1(X42,X40,X44,k9_subset_1(X39,X41,X42))|(~v1_funct_1(X44)|~v1_funct_2(X44,X42,X40)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X40))))|(~v1_funct_1(X43)|~v1_funct_2(X43,X41,X40)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X40))))|(v1_xboole_0(X42)|~m1_subset_1(X42,k1_zfmisc_1(X39)))|(v1_xboole_0(X41)|~m1_subset_1(X41,k1_zfmisc_1(X39)))|v1_xboole_0(X40)|v1_xboole_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.18/0.49  fof(c_0_62, plain, ![X46, X47, X48, X49, X50, X51]:(((v1_funct_1(k1_tmap_1(X46,X47,X48,X49,X50,X51))|(v1_xboole_0(X46)|v1_xboole_0(X47)|v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X46))|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|~v1_funct_1(X51)|~v1_funct_2(X51,X49,X47)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))))&(v1_funct_2(k1_tmap_1(X46,X47,X48,X49,X50,X51),k4_subset_1(X46,X48,X49),X47)|(v1_xboole_0(X46)|v1_xboole_0(X47)|v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X46))|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|~v1_funct_1(X51)|~v1_funct_2(X51,X49,X47)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47))))))&(m1_subset_1(k1_tmap_1(X46,X47,X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X46,X48,X49),X47)))|(v1_xboole_0(X46)|v1_xboole_0(X47)|v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X46))|v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X46))|~v1_funct_1(X50)|~v1_funct_2(X50,X48,X47)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))|~v1_funct_1(X51)|~v1_funct_2(X51,X49,X47)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X47)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.18/0.49  cnf(c_0_63, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k3_xboole_0(esk4_0,X1))=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53])).
% 0.18/0.49  cnf(c_0_64, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.18/0.49  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_66, negated_conjecture, (k7_relat_1(esk5_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_50]), c_0_40])])).
% 0.18/0.49  cnf(c_0_67, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_49]), c_0_48])).
% 0.18/0.49  cnf(c_0_68, negated_conjecture, (k7_relat_1(esk5_0,k3_xboole_0(X1,esk3_0))=k7_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.18/0.49  cnf(c_0_69, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_29])])).
% 0.18/0.49  cnf(c_0_70, plain, (k7_relat_1(k7_relat_1(X1,X2),X3)=k7_relat_1(X1,k3_xboole_0(X2,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.18/0.49  cnf(c_0_71, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_42]), c_0_35])])).
% 0.18/0.49  cnf(c_0_72, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_47]), c_0_48]), c_0_49])).
% 0.18/0.49  cnf(c_0_73, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.49  cnf(c_0_74, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.49  cnf(c_0_75, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.49  cnf(c_0_76, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.49  cnf(c_0_77, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k3_xboole_0(X1,esk4_0))=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.18/0.49  cnf(c_0_78, negated_conjecture, (k9_subset_1(esk1_0,X1,esk4_0)=k3_xboole_0(X1,esk4_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.18/0.49  cnf(c_0_79, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.18/0.49  cnf(c_0_80, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(X1,esk3_0))=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69]), c_0_69])).
% 0.18/0.49  cnf(c_0_81, negated_conjecture, (k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),X2)=k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_40]), c_0_69]), c_0_69])).
% 0.18/0.49  cnf(c_0_82, negated_conjecture, (k7_relat_1(esk6_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.18/0.49  cnf(c_0_83, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_74]), c_0_75]), c_0_76])).
% 0.18/0.49  cnf(c_0_84, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,X1,esk4_0))=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.18/0.49  cnf(c_0_85, negated_conjecture, (~v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_86, negated_conjecture, (k9_subset_1(esk1_0,X1,esk4_0)=k3_xboole_0(esk4_0,X1)), inference(spm,[status(thm)],[c_0_59, c_0_78])).
% 0.18/0.49  cnf(c_0_87, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_79, c_0_69])).
% 0.18/0.49  cnf(c_0_88, negated_conjecture, (k7_relat_1(k2_partfun1(esk3_0,esk2_0,esk5_0,X1),esk3_0)=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_81])).
% 0.18/0.49  cnf(c_0_89, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.18/0.49  cnf(c_0_90, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_91, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k3_xboole_0(esk3_0,X1))=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_69]), c_0_69])).
% 0.18/0.49  cnf(c_0_92, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_82, c_0_53])).
% 0.18/0.49  cnf(c_0_93, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),esk4_0)=esk6_0|v1_xboole_0(X1)|k2_partfun1(X1,esk2_0,X2,k9_subset_1(esk1_0,X1,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)|~v1_funct_2(X2,X1,esk2_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_22]), c_0_23]), c_0_24]), c_0_65])]), c_0_85]), c_0_48]), c_0_25])).
% 0.18/0.49  cnf(c_0_94, negated_conjecture, (k7_relat_1(k1_xboole_0,X1)=k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,X1,esk4_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_86]), c_0_87])).
% 0.18/0.49  cnf(c_0_95, negated_conjecture, (k7_relat_1(k1_xboole_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_87])).
% 0.18/0.49  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.49  cnf(c_0_97, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_89]), c_0_74]), c_0_75]), c_0_76])).
% 0.18/0.49  cnf(c_0_98, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_78]), c_0_78]), c_0_91]), c_0_87]), c_0_77]), c_0_92])])).
% 0.18/0.49  cnf(c_0_99, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95]), c_0_92]), c_0_28]), c_0_29]), c_0_30]), c_0_96])]), c_0_49])).
% 0.18/0.49  cnf(c_0_100, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,X1,esk4_0,X2,esk6_0),X1)=X2|v1_xboole_0(X1)|k2_partfun1(X1,esk2_0,X2,k9_subset_1(esk1_0,X1,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)|~v1_funct_2(X2,X1,esk2_0)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,esk2_0)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_84]), c_0_22]), c_0_23]), c_0_24]), c_0_65])]), c_0_85]), c_0_48]), c_0_25])).
% 0.18/0.49  cnf(c_0_101, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98, c_0_99])])).
% 0.18/0.49  cnf(c_0_102, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_94]), c_0_95]), c_0_92]), c_0_28]), c_0_29]), c_0_30]), c_0_96])]), c_0_101]), c_0_49]), ['proof']).
% 0.18/0.49  # SZS output end CNFRefutation
% 0.18/0.49  # Proof object total steps             : 103
% 0.18/0.49  # Proof object clause steps            : 72
% 0.18/0.49  # Proof object formula steps           : 31
% 0.18/0.49  # Proof object conjectures             : 56
% 0.18/0.49  # Proof object clause conjectures      : 53
% 0.18/0.49  # Proof object formula conjectures     : 3
% 0.18/0.49  # Proof object initial clauses used    : 31
% 0.18/0.49  # Proof object initial formulas used   : 15
% 0.18/0.49  # Proof object generating inferences   : 32
% 0.18/0.49  # Proof object simplifying inferences  : 93
% 0.18/0.49  # Training examples: 0 positive, 0 negative
% 0.18/0.49  # Parsed axioms                        : 15
% 0.18/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.49  # Initial clauses                      : 36
% 0.18/0.49  # Removed in clause preprocessing      : 1
% 0.18/0.49  # Initial clauses in saturation        : 35
% 0.18/0.49  # Processed clauses                    : 1150
% 0.18/0.49  # ...of these trivial                  : 175
% 0.18/0.49  # ...subsumed                          : 346
% 0.18/0.49  # ...remaining for further processing  : 629
% 0.18/0.49  # Other redundant clauses eliminated   : 5
% 0.18/0.49  # Clauses deleted for lack of memory   : 0
% 0.18/0.49  # Backward-subsumed                    : 3
% 0.18/0.49  # Backward-rewritten                   : 74
% 0.18/0.49  # Generated clauses                    : 4201
% 0.18/0.49  # ...of the previous two non-trivial   : 3354
% 0.18/0.49  # Contextual simplify-reflections      : 6
% 0.18/0.49  # Paramodulations                      : 4186
% 0.18/0.49  # Factorizations                       : 0
% 0.18/0.49  # Equation resolutions                 : 16
% 0.18/0.49  # Propositional unsat checks           : 0
% 0.18/0.49  #    Propositional check models        : 0
% 0.18/0.49  #    Propositional check unsatisfiable : 0
% 0.18/0.49  #    Propositional clauses             : 0
% 0.18/0.49  #    Propositional clauses after purity: 0
% 0.18/0.49  #    Propositional unsat core size     : 0
% 0.18/0.49  #    Propositional preprocessing time  : 0.000
% 0.18/0.49  #    Propositional encoding time       : 0.000
% 0.18/0.49  #    Propositional solver time         : 0.000
% 0.18/0.49  #    Success case prop preproc time    : 0.000
% 0.18/0.49  #    Success case prop encoding time   : 0.000
% 0.18/0.49  #    Success case prop solver time     : 0.000
% 0.18/0.49  # Current number of processed clauses  : 513
% 0.18/0.49  #    Positive orientable unit clauses  : 310
% 0.18/0.49  #    Positive unorientable unit clauses: 10
% 0.18/0.49  #    Negative unit clauses             : 5
% 0.18/0.49  #    Non-unit-clauses                  : 188
% 0.18/0.49  # Current number of unprocessed clauses: 2208
% 0.18/0.49  # ...number of literals in the above   : 7625
% 0.18/0.49  # Current number of archived formulas  : 0
% 0.18/0.49  # Current number of archived clauses   : 112
% 0.18/0.49  # Clause-clause subsumption calls (NU) : 21986
% 0.18/0.49  # Rec. Clause-clause subsumption calls : 10357
% 0.18/0.49  # Non-unit clause-clause subsumptions  : 290
% 0.18/0.49  # Unit Clause-clause subsumption calls : 8469
% 0.18/0.49  # Rewrite failures with RHS unbound    : 0
% 0.18/0.49  # BW rewrite match attempts            : 14822
% 0.18/0.49  # BW rewrite match successes           : 196
% 0.18/0.49  # Condensation attempts                : 0
% 0.18/0.49  # Condensation successes               : 0
% 0.18/0.49  # Termbank termtop insertions          : 143503
% 0.18/0.49  
% 0.18/0.49  # -------------------------------------------------
% 0.18/0.49  # User time                : 0.149 s
% 0.18/0.49  # System time              : 0.010 s
% 0.18/0.49  # Total time               : 0.159 s
% 0.18/0.49  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
