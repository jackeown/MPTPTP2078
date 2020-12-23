%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:37 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  124 (2136 expanded)
%              Number of clauses        :   82 ( 822 expanded)
%              Number of leaves         :   21 ( 534 expanded)
%              Depth                    :   16
%              Number of atoms          :  598 (16456 expanded)
%              Number of equality atoms :  123 (2978 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

fof(t1_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & r1_xboole_0(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t103_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r1_tarski(X1,X2)
       => k7_relat_1(k7_relat_1(X3,X2),X1) = k7_relat_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

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

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(c_0_21,negated_conjecture,(
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

fof(c_0_22,plain,(
    ! [X38,X39,X40] :
      ( ( v1_funct_1(X40)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | v1_xboole_0(X39) )
      & ( v1_partfun1(X40,X38)
        | ~ v1_funct_1(X40)
        | ~ v1_funct_2(X40,X38,X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
        | v1_xboole_0(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_23,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))
    & r1_subset_1(esk4_0,esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk3_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk3_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))
    & ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
      | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
      | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_24,plain,(
    ! [X33,X34,X35] :
      ( ( v4_relat_1(X35,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( v5_relat_1(X35,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_25,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_26,plain,(
    ! [X41,X42] :
      ( ( ~ v1_partfun1(X42,X41)
        | k1_relat_1(X42) = X41
        | ~ v1_relat_1(X42)
        | ~ v4_relat_1(X42,X41) )
      & ( k1_relat_1(X42) != X41
        | v1_partfun1(X42,X41)
        | ~ v1_relat_1(X42)
        | ~ v4_relat_1(X42,X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_27,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_34,plain,(
    ! [X22,X23] :
      ( ~ v1_relat_1(X22)
      | ~ r1_xboole_0(X23,k1_relat_1(X22))
      | k7_relat_1(X22,X23) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

fof(c_0_39,plain,(
    ! [X28,X29] :
      ( ( ~ r1_subset_1(X28,X29)
        | r1_xboole_0(X28,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29) )
      & ( ~ r1_xboole_0(X28,X29)
        | r1_subset_1(X28,X29)
        | v1_xboole_0(X28)
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_40,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_42,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_46,plain,(
    ! [X36] :
      ( ( r2_hidden(esk1_1(X36),X36)
        | X36 = k1_xboole_0 )
      & ( r1_xboole_0(esk1_1(X36),X36)
        | X36 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).

fof(c_0_47,plain,(
    ! [X27] :
      ( ~ v1_relat_1(X27)
      | k7_relat_1(X27,k1_relat_1(X27)) = X27 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_48,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_38])])).

cnf(c_0_50,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

fof(c_0_51,plain,(
    ! [X25,X26] :
      ( ~ v1_relat_1(X26)
      | r1_tarski(k1_relat_1(k7_relat_1(X26,X25)),X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_52,plain,
    ( r1_xboole_0(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_55,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_57,plain,(
    ! [X19,X20,X21] :
      ( ~ v1_relat_1(X21)
      | ~ r1_tarski(X19,X20)
      | k7_relat_1(k7_relat_1(X21,X20),X19) = k7_relat_1(X21,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).

cnf(c_0_58,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( k7_relat_1(X1,esk1_1(k1_relat_1(X1))) = k1_xboole_0
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_52])).

fof(c_0_60,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( ( v1_funct_1(k1_tmap_1(X54,X55,X56,X57,X58,X59))
        | v1_xboole_0(X54)
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(X54))
        | v1_xboole_0(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X54))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X55)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X57,X55)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55))) )
      & ( v1_funct_2(k1_tmap_1(X54,X55,X56,X57,X58,X59),k4_subset_1(X54,X56,X57),X55)
        | v1_xboole_0(X54)
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(X54))
        | v1_xboole_0(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X54))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X55)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X57,X55)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55))) )
      & ( m1_subset_1(k1_tmap_1(X54,X55,X56,X57,X58,X59),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X54,X56,X57),X55)))
        | v1_xboole_0(X54)
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | ~ m1_subset_1(X56,k1_zfmisc_1(X54))
        | v1_xboole_0(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X54))
        | ~ v1_funct_1(X58)
        | ~ v1_funct_2(X58,X56,X55)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X57,X55)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_61,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_62,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_63,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_64,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ v1_funct_1(X45)
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k2_partfun1(X43,X44,X45,X46) = k7_relat_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_65,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_38])])).

cnf(c_0_67,plain,
    ( k7_relat_1(k7_relat_1(X1,X3),X2) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_68,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | r1_tarski(k1_xboole_0,esk1_1(k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_54])).

fof(c_0_69,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53] :
      ( ( k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X49) = X51
        | X53 != k1_tmap_1(X47,X48,X49,X50,X51,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,k4_subset_1(X47,X49,X50),X48)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X47,X49,X50),X48)))
        | k2_partfun1(X49,X48,X51,k9_subset_1(X47,X49,X50)) != k2_partfun1(X50,X48,X52,k9_subset_1(X47,X49,X50))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X48)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X47))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) )
      & ( k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X50) = X52
        | X53 != k1_tmap_1(X47,X48,X49,X50,X51,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,k4_subset_1(X47,X49,X50),X48)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X47,X49,X50),X48)))
        | k2_partfun1(X49,X48,X51,k9_subset_1(X47,X49,X50)) != k2_partfun1(X50,X48,X52,k9_subset_1(X47,X49,X50))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X48)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X47))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) )
      & ( k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X49) != X51
        | k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X50) != X52
        | X53 = k1_tmap_1(X47,X48,X49,X50,X51,X52)
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,k4_subset_1(X47,X49,X50),X48)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X47,X49,X50),X48)))
        | k2_partfun1(X49,X48,X51,k9_subset_1(X47,X49,X50)) != k2_partfun1(X50,X48,X52,k9_subset_1(X47,X49,X50))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X48)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X48)))
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,X49,X48)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48)))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X47))
        | v1_xboole_0(X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(X47))
        | v1_xboole_0(X48)
        | v1_xboole_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_70,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_71,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_72,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_74,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_76,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_77,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

fof(c_0_79,plain,(
    ! [X24] :
      ( ( k1_relat_1(X24) != k1_xboole_0
        | X24 = k1_xboole_0
        | ~ v1_relat_1(X24) )
      & ( k2_relat_1(X24) != k1_xboole_0
        | X24 = k1_xboole_0
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_80,plain,
    ( k7_relat_1(k7_relat_1(X1,esk1_1(k1_relat_1(X2))),k1_xboole_0) = k7_relat_1(X1,k1_xboole_0)
    | k1_relat_1(X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_81,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_82,plain,
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
    inference(csr,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_83,plain,
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
    inference(csr,[status(thm)],[c_0_72,c_0_71])).

cnf(c_0_84,plain,
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
    inference(csr,[status(thm)],[c_0_73,c_0_71])).

cnf(c_0_85,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_87,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_56]),c_0_54]),c_0_38])])).

cnf(c_0_89,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k2_partfun1(esk5_0,esk3_0,esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_30]),c_0_29])])).

cnf(c_0_90,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_78]),c_0_54]),c_0_66])])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_92,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | k1_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_59]),c_0_78])).

cnf(c_0_93,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_81,c_0_71])]),c_0_82]),c_0_83]),c_0_84])).

cnf(c_0_94,negated_conjecture,
    ( k9_subset_1(esk2_0,X1,esk5_0) = k1_setfam_1(k2_tarski(X1,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_95,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_87,c_0_75])).

cnf(c_0_96,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_97,negated_conjecture,
    ( k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0) = k7_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_56,c_0_89])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_100,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_101,plain,
    ( k7_relat_1(k7_relat_1(X1,k1_xboole_0),k1_xboole_0) = k7_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_90])).

cnf(c_0_102,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0) = X4
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0))) != k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_86])]),c_0_44])).

cnf(c_0_104,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,esk5_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_95,c_0_50])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_106,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_96,c_0_71])]),c_0_82]),c_0_83]),c_0_84])).

cnf(c_0_107,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_108,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_89]),c_0_98]),c_0_78]),c_0_89]),c_0_38])])).

cnf(c_0_109,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk3_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_99]),c_0_100])])).

cnf(c_0_110,plain,
    ( k7_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_55])).

cnf(c_0_111,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_99])).

cnf(c_0_112,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0) = X3
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_105])]),c_0_45])).

cnf(c_0_113,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1) = X3
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0))) != k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))
    | ~ v1_funct_2(X4,esk5_0,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_94]),c_0_86])]),c_0_44])).

cnf(c_0_114,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0
    | k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_94]),c_0_104]),c_0_108]),c_0_94]),c_0_104])).

cnf(c_0_115,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_111])])).

cnf(c_0_116,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,X1,esk7_0),esk5_0) = esk7_0
    | k2_partfun1(esk4_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk4_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_108]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_117,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_118,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(esk4_0,X1,X2,k1_xboole_0) != k2_partfun1(esk5_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk5_0,X1)
    | ~ v1_funct_2(X2,esk4_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_104]),c_0_105])]),c_0_45])).

cnf(c_0_119,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114,c_0_115])])).

cnf(c_0_120,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_115]),c_0_117]),c_0_100]),c_0_99])])).

cnf(c_0_121,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk4_0) = esk6_0
    | k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk5_0,esk3_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_115]),c_0_117]),c_0_100]),c_0_99])]),c_0_31])).

cnf(c_0_122,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120])])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_108]),c_0_28]),c_0_29]),c_0_30])]),c_0_122]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.39/0.58  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.39/0.58  # and selection function SelectCQIPrecWNTNp.
% 0.39/0.58  #
% 0.39/0.58  # Preprocessing time       : 0.030 s
% 0.39/0.58  # Presaturation interreduction done
% 0.39/0.58  
% 0.39/0.58  # Proof found!
% 0.39/0.58  # SZS status Theorem
% 0.39/0.58  # SZS output start CNFRefutation
% 0.39/0.58  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.39/0.58  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.39/0.58  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.39/0.58  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.39/0.58  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.39/0.58  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.39/0.58  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.39/0.58  fof(t1_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&r1_xboole_0(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 0.39/0.58  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.39/0.58  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.39/0.58  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.39/0.58  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.39/0.58  fof(t103_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r1_tarski(X1,X2)=>k7_relat_1(k7_relat_1(X3,X2),X1)=k7_relat_1(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 0.39/0.58  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.39/0.58  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.39/0.58  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.39/0.58  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.39/0.58  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.39/0.58  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.39/0.58  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.39/0.58  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.39/0.58  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.39/0.58  fof(c_0_22, plain, ![X38, X39, X40]:((v1_funct_1(X40)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_xboole_0(X39))&(v1_partfun1(X40,X38)|(~v1_funct_1(X40)|~v1_funct_2(X40,X38,X39))|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|v1_xboole_0(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.39/0.58  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 0.39/0.58  fof(c_0_24, plain, ![X33, X34, X35]:((v4_relat_1(X35,X33)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))&(v5_relat_1(X35,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.39/0.58  fof(c_0_25, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.39/0.58  fof(c_0_26, plain, ![X41, X42]:((~v1_partfun1(X42,X41)|k1_relat_1(X42)=X41|(~v1_relat_1(X42)|~v4_relat_1(X42,X41)))&(k1_relat_1(X42)!=X41|v1_partfun1(X42,X41)|(~v1_relat_1(X42)|~v4_relat_1(X42,X41)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.39/0.58  cnf(c_0_27, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.39/0.58  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_32, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.39/0.58  cnf(c_0_33, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.39/0.58  fof(c_0_34, plain, ![X22, X23]:(~v1_relat_1(X22)|(~r1_xboole_0(X23,k1_relat_1(X22))|k7_relat_1(X22,X23)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.39/0.58  cnf(c_0_35, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.58  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.39/0.58  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 0.39/0.58  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 0.39/0.58  fof(c_0_39, plain, ![X28, X29]:((~r1_subset_1(X28,X29)|r1_xboole_0(X28,X29)|(v1_xboole_0(X28)|v1_xboole_0(X29)))&(~r1_xboole_0(X28,X29)|r1_subset_1(X28,X29)|(v1_xboole_0(X28)|v1_xboole_0(X29)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.39/0.58  cnf(c_0_40, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.58  cnf(c_0_41, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 0.39/0.58  cnf(c_0_42, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.39/0.58  cnf(c_0_43, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_44, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  fof(c_0_46, plain, ![X36]:((r2_hidden(esk1_1(X36),X36)|X36=k1_xboole_0)&(r1_xboole_0(esk1_1(X36),X36)|X36=k1_xboole_0)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_mcart_1])])])])).
% 0.39/0.58  fof(c_0_47, plain, ![X27]:(~v1_relat_1(X27)|k7_relat_1(X27,k1_relat_1(X27))=X27), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.39/0.58  fof(c_0_48, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.39/0.58  cnf(c_0_49, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_38])])).
% 0.39/0.58  cnf(c_0_50, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])).
% 0.39/0.58  fof(c_0_51, plain, ![X25, X26]:(~v1_relat_1(X26)|r1_tarski(k1_relat_1(k7_relat_1(X26,X25)),X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.39/0.58  cnf(c_0_52, plain, (r1_xboole_0(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.39/0.58  cnf(c_0_53, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.39/0.58  cnf(c_0_54, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.39/0.58  cnf(c_0_55, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.39/0.58  cnf(c_0_56, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.39/0.58  fof(c_0_57, plain, ![X19, X20, X21]:(~v1_relat_1(X21)|(~r1_tarski(X19,X20)|k7_relat_1(k7_relat_1(X21,X20),X19)=k7_relat_1(X21,X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t103_relat_1])])).
% 0.39/0.58  cnf(c_0_58, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.58  cnf(c_0_59, plain, (k7_relat_1(X1,esk1_1(k1_relat_1(X1)))=k1_xboole_0|k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_40, c_0_52])).
% 0.39/0.58  fof(c_0_60, plain, ![X54, X55, X56, X57, X58, X59]:(((v1_funct_1(k1_tmap_1(X54,X55,X56,X57,X58,X59))|(v1_xboole_0(X54)|v1_xboole_0(X55)|v1_xboole_0(X56)|~m1_subset_1(X56,k1_zfmisc_1(X54))|v1_xboole_0(X57)|~m1_subset_1(X57,k1_zfmisc_1(X54))|~v1_funct_1(X58)|~v1_funct_2(X58,X56,X55)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))|~v1_funct_1(X59)|~v1_funct_2(X59,X57,X55)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55)))))&(v1_funct_2(k1_tmap_1(X54,X55,X56,X57,X58,X59),k4_subset_1(X54,X56,X57),X55)|(v1_xboole_0(X54)|v1_xboole_0(X55)|v1_xboole_0(X56)|~m1_subset_1(X56,k1_zfmisc_1(X54))|v1_xboole_0(X57)|~m1_subset_1(X57,k1_zfmisc_1(X54))|~v1_funct_1(X58)|~v1_funct_2(X58,X56,X55)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))|~v1_funct_1(X59)|~v1_funct_2(X59,X57,X55)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55))))))&(m1_subset_1(k1_tmap_1(X54,X55,X56,X57,X58,X59),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X54,X56,X57),X55)))|(v1_xboole_0(X54)|v1_xboole_0(X55)|v1_xboole_0(X56)|~m1_subset_1(X56,k1_zfmisc_1(X54))|v1_xboole_0(X57)|~m1_subset_1(X57,k1_zfmisc_1(X54))|~v1_funct_1(X58)|~v1_funct_2(X58,X56,X55)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X55)))|~v1_funct_1(X59)|~v1_funct_2(X59,X57,X55)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.39/0.58  fof(c_0_61, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.39/0.58  fof(c_0_62, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.39/0.58  fof(c_0_63, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.39/0.58  fof(c_0_64, plain, ![X43, X44, X45, X46]:(~v1_funct_1(X45)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k2_partfun1(X43,X44,X45,X46)=k7_relat_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.39/0.58  cnf(c_0_65, plain, (k7_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.39/0.58  cnf(c_0_66, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_38])])).
% 0.39/0.58  cnf(c_0_67, plain, (k7_relat_1(k7_relat_1(X1,X3),X2)=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.39/0.58  cnf(c_0_68, plain, (k1_relat_1(X1)=k1_xboole_0|r1_tarski(k1_xboole_0,esk1_1(k1_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_54])).
% 0.39/0.58  fof(c_0_69, plain, ![X47, X48, X49, X50, X51, X52, X53]:(((k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X49)=X51|X53!=k1_tmap_1(X47,X48,X49,X50,X51,X52)|(~v1_funct_1(X53)|~v1_funct_2(X53,k4_subset_1(X47,X49,X50),X48)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X47,X49,X50),X48))))|k2_partfun1(X49,X48,X51,k9_subset_1(X47,X49,X50))!=k2_partfun1(X50,X48,X52,k9_subset_1(X47,X49,X50))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X48)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X48))))|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48))))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X47)))|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X47)))|v1_xboole_0(X48)|v1_xboole_0(X47))&(k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X50)=X52|X53!=k1_tmap_1(X47,X48,X49,X50,X51,X52)|(~v1_funct_1(X53)|~v1_funct_2(X53,k4_subset_1(X47,X49,X50),X48)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X47,X49,X50),X48))))|k2_partfun1(X49,X48,X51,k9_subset_1(X47,X49,X50))!=k2_partfun1(X50,X48,X52,k9_subset_1(X47,X49,X50))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X48)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X48))))|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48))))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X47)))|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X47)))|v1_xboole_0(X48)|v1_xboole_0(X47)))&(k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X49)!=X51|k2_partfun1(k4_subset_1(X47,X49,X50),X48,X53,X50)!=X52|X53=k1_tmap_1(X47,X48,X49,X50,X51,X52)|(~v1_funct_1(X53)|~v1_funct_2(X53,k4_subset_1(X47,X49,X50),X48)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X47,X49,X50),X48))))|k2_partfun1(X49,X48,X51,k9_subset_1(X47,X49,X50))!=k2_partfun1(X50,X48,X52,k9_subset_1(X47,X49,X50))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X48)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X48))))|(~v1_funct_1(X51)|~v1_funct_2(X51,X49,X48)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X48))))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X47)))|(v1_xboole_0(X49)|~m1_subset_1(X49,k1_zfmisc_1(X47)))|v1_xboole_0(X48)|v1_xboole_0(X47))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.39/0.58  cnf(c_0_70, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.58  cnf(c_0_71, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.39/0.58  cnf(c_0_72, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.58  cnf(c_0_73, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.39/0.58  cnf(c_0_74, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.39/0.58  cnf(c_0_75, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.39/0.58  fof(c_0_76, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.39/0.58  cnf(c_0_77, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.39/0.58  cnf(c_0_78, plain, (k7_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65, c_0_66])])).
% 0.39/0.58  fof(c_0_79, plain, ![X24]:((k1_relat_1(X24)!=k1_xboole_0|X24=k1_xboole_0|~v1_relat_1(X24))&(k2_relat_1(X24)!=k1_xboole_0|X24=k1_xboole_0|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.39/0.58  cnf(c_0_80, plain, (k7_relat_1(k7_relat_1(X1,esk1_1(k1_relat_1(X2))),k1_xboole_0)=k7_relat_1(X1,k1_xboole_0)|k1_relat_1(X2)=k1_xboole_0|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.39/0.58  cnf(c_0_81, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.39/0.58  cnf(c_0_82, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_70, c_0_71])).
% 0.39/0.58  cnf(c_0_83, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_72, c_0_71])).
% 0.39/0.58  cnf(c_0_84, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_73, c_0_71])).
% 0.39/0.58  cnf(c_0_85, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.39/0.58  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_87, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.39/0.58  cnf(c_0_88, negated_conjecture, (r1_tarski(k1_xboole_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_56]), c_0_54]), c_0_38])])).
% 0.39/0.58  cnf(c_0_89, negated_conjecture, (k7_relat_1(esk7_0,X1)=k2_partfun1(esk5_0,esk3_0,esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_30]), c_0_29])])).
% 0.39/0.58  cnf(c_0_90, plain, (r1_tarski(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_78]), c_0_54]), c_0_66])])).
% 0.39/0.58  cnf(c_0_91, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.39/0.58  cnf(c_0_92, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|k1_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_59]), c_0_78])).
% 0.39/0.58  cnf(c_0_93, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_81, c_0_71])]), c_0_82]), c_0_83]), c_0_84])).
% 0.39/0.58  cnf(c_0_94, negated_conjecture, (k9_subset_1(esk2_0,X1,esk5_0)=k1_setfam_1(k2_tarski(X1,esk5_0))), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.39/0.58  cnf(c_0_95, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_87, c_0_75])).
% 0.39/0.58  cnf(c_0_96, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.39/0.58  cnf(c_0_97, negated_conjecture, (k7_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0)=k7_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_88])).
% 0.39/0.58  cnf(c_0_98, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_56, c_0_89])).
% 0.39/0.58  cnf(c_0_99, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_100, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_101, plain, (k7_relat_1(k7_relat_1(X1,k1_xboole_0),k1_xboole_0)=k7_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_90])).
% 0.39/0.58  cnf(c_0_102, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|X1=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.39/0.58  cnf(c_0_103, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),esk5_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0)))!=k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_86])]), c_0_44])).
% 0.39/0.58  cnf(c_0_104, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,esk5_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_95, c_0_50])).
% 0.39/0.58  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_106, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_96, c_0_71])]), c_0_82]), c_0_83]), c_0_84])).
% 0.39/0.58  cnf(c_0_107, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_108, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_89]), c_0_98]), c_0_78]), c_0_89]), c_0_38])])).
% 0.39/0.58  cnf(c_0_109, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk3_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_99]), c_0_100])])).
% 0.39/0.58  cnf(c_0_110, plain, (k7_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_55])).
% 0.39/0.58  cnf(c_0_111, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_99])).
% 0.39/0.58  cnf(c_0_112, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk5_0)=X3|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_105])]), c_0_45])).
% 0.39/0.58  cnf(c_0_113, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,X1,esk5_0),X2,k1_tmap_1(esk2_0,X2,X1,esk5_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk5_0)))!=k2_partfun1(esk5_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk5_0)))|~v1_funct_2(X4,esk5_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_94]), c_0_86])]), c_0_44])).
% 0.39/0.58  cnf(c_0_114, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0|k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_94]), c_0_104]), c_0_108]), c_0_94]), c_0_104])).
% 0.39/0.58  cnf(c_0_115, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_111])])).
% 0.39/0.58  cnf(c_0_116, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,X1,esk7_0),esk5_0)=esk7_0|k2_partfun1(esk4_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk4_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_108]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 0.39/0.58  cnf(c_0_117, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.39/0.58  cnf(c_0_118, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),X1,k1_tmap_1(esk2_0,X1,esk4_0,esk5_0,X2,X3),esk4_0)=X2|v1_xboole_0(X1)|k2_partfun1(esk4_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk5_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk5_0,X1)|~v1_funct_2(X2,esk4_0,X1)|~v1_funct_1(X3)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk5_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_104]), c_0_105])]), c_0_45])).
% 0.39/0.58  cnf(c_0_119, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_114, c_0_115])])).
% 0.39/0.58  cnf(c_0_120, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_115]), c_0_117]), c_0_100]), c_0_99])])).
% 0.39/0.58  cnf(c_0_121, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,X1),esk4_0)=esk6_0|k2_partfun1(esk5_0,esk3_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk5_0,esk3_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_115]), c_0_117]), c_0_100]), c_0_99])]), c_0_31])).
% 0.39/0.58  cnf(c_0_122, negated_conjecture, (k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120])])).
% 0.39/0.58  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121, c_0_108]), c_0_28]), c_0_29]), c_0_30])]), c_0_122]), ['proof']).
% 0.39/0.58  # SZS output end CNFRefutation
% 0.39/0.58  # Proof object total steps             : 124
% 0.39/0.58  # Proof object clause steps            : 82
% 0.39/0.58  # Proof object formula steps           : 42
% 0.39/0.58  # Proof object conjectures             : 45
% 0.39/0.58  # Proof object clause conjectures      : 42
% 0.39/0.58  # Proof object formula conjectures     : 3
% 0.39/0.58  # Proof object initial clauses used    : 36
% 0.39/0.58  # Proof object initial formulas used   : 21
% 0.39/0.58  # Proof object generating inferences   : 34
% 0.39/0.58  # Proof object simplifying inferences  : 91
% 0.39/0.58  # Training examples: 0 positive, 0 negative
% 0.39/0.58  # Parsed axioms                        : 21
% 0.39/0.58  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.58  # Initial clauses                      : 46
% 0.39/0.58  # Removed in clause preprocessing      : 2
% 0.39/0.58  # Initial clauses in saturation        : 44
% 0.39/0.58  # Processed clauses                    : 1861
% 0.39/0.58  # ...of these trivial                  : 54
% 0.39/0.58  # ...subsumed                          : 1108
% 0.39/0.58  # ...remaining for further processing  : 699
% 0.39/0.58  # Other redundant clauses eliminated   : 5
% 0.39/0.58  # Clauses deleted for lack of memory   : 0
% 0.39/0.58  # Backward-subsumed                    : 5
% 0.39/0.58  # Backward-rewritten                   : 56
% 0.39/0.58  # Generated clauses                    : 8954
% 0.39/0.58  # ...of the previous two non-trivial   : 6165
% 0.39/0.58  # Contextual simplify-reflections      : 58
% 0.39/0.58  # Paramodulations                      : 8940
% 0.39/0.58  # Factorizations                       : 0
% 0.39/0.58  # Equation resolutions                 : 15
% 0.39/0.58  # Propositional unsat checks           : 0
% 0.39/0.58  #    Propositional check models        : 0
% 0.39/0.58  #    Propositional check unsatisfiable : 0
% 0.39/0.58  #    Propositional clauses             : 0
% 0.39/0.58  #    Propositional clauses after purity: 0
% 0.39/0.58  #    Propositional unsat core size     : 0
% 0.39/0.58  #    Propositional preprocessing time  : 0.000
% 0.39/0.58  #    Propositional encoding time       : 0.000
% 0.39/0.58  #    Propositional solver time         : 0.000
% 0.39/0.58  #    Success case prop preproc time    : 0.000
% 0.39/0.58  #    Success case prop encoding time   : 0.000
% 0.39/0.58  #    Success case prop solver time     : 0.000
% 0.39/0.58  # Current number of processed clauses  : 590
% 0.39/0.58  #    Positive orientable unit clauses  : 177
% 0.39/0.58  #    Positive unorientable unit clauses: 2
% 0.39/0.58  #    Negative unit clauses             : 5
% 0.39/0.58  #    Non-unit-clauses                  : 406
% 0.39/0.58  # Current number of unprocessed clauses: 4309
% 0.39/0.58  # ...number of literals in the above   : 14926
% 0.39/0.58  # Current number of archived formulas  : 0
% 0.39/0.58  # Current number of archived clauses   : 106
% 0.39/0.58  # Clause-clause subsumption calls (NU) : 147796
% 0.39/0.58  # Rec. Clause-clause subsumption calls : 52612
% 0.39/0.58  # Non-unit clause-clause subsumptions  : 1168
% 0.39/0.58  # Unit Clause-clause subsumption calls : 17245
% 0.39/0.58  # Rewrite failures with RHS unbound    : 0
% 0.39/0.58  # BW rewrite match attempts            : 680
% 0.39/0.58  # BW rewrite match successes           : 41
% 0.39/0.58  # Condensation attempts                : 0
% 0.39/0.58  # Condensation successes               : 0
% 0.39/0.58  # Termbank termtop insertions          : 302683
% 0.39/0.58  
% 0.39/0.58  # -------------------------------------------------
% 0.39/0.58  # User time                : 0.228 s
% 0.39/0.58  # System time              : 0.009 s
% 0.39/0.58  # Total time               : 0.237 s
% 0.39/0.58  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
