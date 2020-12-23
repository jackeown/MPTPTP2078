%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:37 EST 2020

% Result     : Theorem 12.10s
% Output     : CNFRefutation 12.10s
% Verified   : 
% Statistics : Number of formulae       :  134 (3320 expanded)
%              Number of clauses        :   92 (1247 expanded)
%              Number of leaves         :   21 ( 825 expanded)
%              Depth                    :   18
%              Number of atoms          :  603 (26668 expanded)
%              Number of equality atoms :  117 (4706 expanded)
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

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

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

fof(t151_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

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
    ! [X39,X40,X41] :
      ( ( v1_funct_1(X41)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | v1_xboole_0(X40) )
      & ( v1_partfun1(X41,X39)
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | v1_xboole_0(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_23,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).

fof(c_0_24,plain,(
    ! [X36,X37,X38] :
      ( ( v4_relat_1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v5_relat_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_25,plain,(
    ! [X33,X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | v1_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_26,plain,(
    ! [X42,X43] :
      ( ( ~ v1_partfun1(X43,X42)
        | k1_relat_1(X43) = X42
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) )
      & ( k1_relat_1(X43) != X42
        | v1_partfun1(X43,X42)
        | ~ v1_relat_1(X43)
        | ~ v4_relat_1(X43,X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_27,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
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
    ! [X25,X26] :
      ( ~ v1_relat_1(X25)
      | ~ r1_xboole_0(X26,k1_relat_1(X25))
      | k7_relat_1(X25,X26) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_35,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_30])).

fof(c_0_39,plain,(
    ! [X31,X32] :
      ( ( ~ r1_subset_1(X31,X32)
        | r1_xboole_0(X31,X32)
        | v1_xboole_0(X31)
        | v1_xboole_0(X32) )
      & ( ~ r1_xboole_0(X31,X32)
        | r1_subset_1(X31,X32)
        | v1_xboole_0(X31)
        | v1_xboole_0(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk5_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_43,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_45,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_subset_1(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_49,negated_conjecture,
    ( v1_partfun1(esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_40]),c_0_41]),c_0_42])]),c_0_31])).

cnf(c_0_50,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_42])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_42])).

fof(c_0_52,plain,(
    ! [X29,X30] :
      ( ( k7_relat_1(X30,X29) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_xboole_0(k1_relat_1(X30),X29)
        | k7_relat_1(X30,X29) = k1_xboole_0
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

cnf(c_0_53,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_38])])).

cnf(c_0_54,negated_conjecture,
    ( r1_xboole_0(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_56,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(esk6_0,esk3_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_58,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X28)
      | r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_59,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_55]),c_0_51])])).

cnf(c_0_60,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_44]),c_0_38])])).

fof(c_0_61,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ v1_funct_1(X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k2_partfun1(X44,X45,X46,X47) = k7_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_62,plain,(
    ! [X19] :
      ( ~ v1_relat_1(X19)
      | k9_relat_1(X19,k1_relat_1(X19)) = k2_relat_1(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

fof(c_0_63,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | v1_relat_1(k7_relat_1(X17,X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_64,plain,(
    ! [X55,X56,X57,X58,X59,X60] :
      ( ( v1_funct_1(k1_tmap_1(X55,X56,X57,X58,X59,X60))
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X55))
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X55))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X57,X56)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X56)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X56))) )
      & ( v1_funct_2(k1_tmap_1(X55,X56,X57,X58,X59,X60),k4_subset_1(X55,X57,X58),X56)
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X55))
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X55))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X57,X56)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X56)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X56))) )
      & ( m1_subset_1(k1_tmap_1(X55,X56,X57,X58,X59,X60),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X55,X57,X58),X56)))
        | v1_xboole_0(X55)
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | ~ m1_subset_1(X57,k1_zfmisc_1(X55))
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X55))
        | ~ v1_funct_1(X59)
        | ~ v1_funct_2(X59,X57,X56)
        | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X56)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_65,plain,(
    ! [X13,X14] :
      ( ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | v1_xboole_0(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_66,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_67,plain,(
    ! [X15,X16] : k1_setfam_1(k2_tarski(X15,X16)) = k3_xboole_0(X15,X16) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_68,plain,(
    ! [X22,X23,X24] :
      ( ~ v1_relat_1(X22)
      | ~ r1_tarski(X23,X24)
      | k9_relat_1(k7_relat_1(X22,X24),X23) = k9_relat_1(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_69,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( k7_relat_1(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_72,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_73,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_74,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

fof(c_0_76,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54] :
      ( ( k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X50) = X52
        | X54 != k1_tmap_1(X48,X49,X50,X51,X52,X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,k4_subset_1(X48,X50,X51),X49)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))
        | k2_partfun1(X50,X49,X52,k9_subset_1(X48,X50,X51)) != k2_partfun1(X51,X49,X53,k9_subset_1(X48,X50,X51))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) )
      & ( k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X51) = X53
        | X54 != k1_tmap_1(X48,X49,X50,X51,X52,X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,k4_subset_1(X48,X50,X51),X49)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))
        | k2_partfun1(X50,X49,X52,k9_subset_1(X48,X50,X51)) != k2_partfun1(X51,X49,X53,k9_subset_1(X48,X50,X51))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) )
      & ( k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X50) != X52
        | k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X51) != X53
        | X54 = k1_tmap_1(X48,X49,X50,X51,X52,X53)
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,k4_subset_1(X48,X50,X51),X49)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49)))
        | k2_partfun1(X50,X49,X52,k9_subset_1(X48,X50,X51)) != k2_partfun1(X51,X49,X53,k9_subset_1(X48,X50,X51))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X49)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49)))
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,X50,X49)
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X48))
        | v1_xboole_0(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(X48))
        | v1_xboole_0(X49)
        | v1_xboole_0(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

cnf(c_0_77,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_78,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_79,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_80,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_81,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_82,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_83,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_84,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_51])])).

cnf(c_0_86,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k2_partfun1(esk3_0,esk2_0,esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_42]),c_0_41])])).

cnf(c_0_87,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_71])).

cnf(c_0_88,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_57]),c_0_38])])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k1_xboole_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_57]),c_0_71]),c_0_38])])).

cnf(c_0_90,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k2_partfun1(esk4_0,esk2_0,esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_30]),c_0_29])])).

cnf(c_0_91,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_92,plain,
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
    inference(csr,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_93,plain,
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
    inference(csr,[status(thm)],[c_0_79,c_0_78])).

cnf(c_0_94,plain,
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
    inference(csr,[status(thm)],[c_0_80,c_0_78])).

cnf(c_0_95,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_97,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_98,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_99,plain,(
    ! [X20,X21] :
      ( ( k9_relat_1(X21,X20) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X21),X20)
        | ~ v1_relat_1(X21) )
      & ( ~ r1_xboole_0(k1_relat_1(X21),X20)
        | k9_relat_1(X21,X20) = k1_xboole_0
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).

cnf(c_0_100,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0) = k9_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_101,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_70,c_0_86])).

cnf(c_0_102,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87,c_0_88])])).

cnf(c_0_103,negated_conjecture,
    ( k9_relat_1(k7_relat_1(X1,esk3_0),k1_xboole_0) = k9_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_89])).

cnf(c_0_104,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,esk3_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_57,c_0_90])).

cnf(c_0_105,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_91,c_0_78])]),c_0_92]),c_0_93]),c_0_94])).

cnf(c_0_106,negated_conjecture,
    ( k9_subset_1(esk1_0,X1,esk4_0) = k1_setfam_1(k2_tarski(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_107,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_97,c_0_82])).

cnf(c_0_108,negated_conjecture,
    ( k7_relat_1(esk5_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_55]),c_0_51])])).

cnf(c_0_109,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k9_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_99])).

cnf(c_0_110,negated_conjecture,
    ( k9_relat_1(esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_86]),c_0_101]),c_0_102]),c_0_51])])).

cnf(c_0_111,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_112,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_44]),c_0_38])])).

cnf(c_0_113,negated_conjecture,
    ( k9_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_90]),c_0_104]),c_0_102]),c_0_38])])).

cnf(c_0_114,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_96])]),c_0_47])).

cnf(c_0_115,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk3_0,esk4_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_107,c_0_54])).

cnf(c_0_116,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_117,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(esk3_0,X1) ),
    inference(rw,[status(thm)],[c_0_108,c_0_86])).

cnf(c_0_118,negated_conjecture,
    ( r1_xboole_0(esk3_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_55]),c_0_51])])).

cnf(c_0_119,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_111,c_0_78])]),c_0_92]),c_0_93]),c_0_94])).

cnf(c_0_120,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(esk4_0,X1) ),
    inference(rw,[status(thm)],[c_0_112,c_0_90])).

cnf(c_0_121,negated_conjecture,
    ( r1_xboole_0(esk4_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_113]),c_0_44]),c_0_38])])).

cnf(c_0_122,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk3_0) = X2
    | v1_xboole_0(X1)
    | k2_partfun1(esk3_0,X1,X2,k1_xboole_0) != k2_partfun1(esk4_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk4_0,X1)
    | ~ v1_funct_2(X2,esk3_0,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_116])]),c_0_48])).

cnf(c_0_123,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_124,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_106]),c_0_96])]),c_0_47])).

cnf(c_0_125,negated_conjecture,
    ( k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0)) != k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_126,negated_conjecture,
    ( k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_120,c_0_121])).

cnf(c_0_127,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,X1),esk3_0) = esk5_0
    | k2_partfun1(esk4_0,esk2_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk4_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122,c_0_123]),c_0_40]),c_0_41]),c_0_42])]),c_0_31])).

cnf(c_0_128,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk4_0) = X3
    | v1_xboole_0(X1)
    | k2_partfun1(esk3_0,X1,X2,k1_xboole_0) != k2_partfun1(esk4_0,X1,X3,k1_xboole_0)
    | ~ v1_funct_2(X3,esk4_0,X1)
    | ~ v1_funct_2(X2,esk3_0,X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_115]),c_0_116])]),c_0_48])).

cnf(c_0_129,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) != esk5_0
    | k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125,c_0_106]),c_0_115]),c_0_126]),c_0_106]),c_0_115]),c_0_123])])).

cnf(c_0_130,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_126]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_131,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,X1,esk6_0),esk4_0) = esk6_0
    | k2_partfun1(esk3_0,esk2_0,X1,k1_xboole_0) != k1_xboole_0
    | ~ v1_funct_2(X1,esk3_0,esk2_0)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_126]),c_0_28]),c_0_29]),c_0_30])]),c_0_31])).

cnf(c_0_132,negated_conjecture,
    ( k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0) != esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129,c_0_130])])).

cnf(c_0_133,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_123]),c_0_40]),c_0_41]),c_0_42])]),c_0_132]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:50:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 12.10/12.28  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 12.10/12.28  # and selection function SelectCQIPrecWNTNp.
% 12.10/12.28  #
% 12.10/12.28  # Preprocessing time       : 0.030 s
% 12.10/12.28  # Presaturation interreduction done
% 12.10/12.28  
% 12.10/12.28  # Proof found!
% 12.10/12.28  # SZS status Theorem
% 12.10/12.28  # SZS output start CNFRefutation
% 12.10/12.28  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 12.10/12.28  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 12.10/12.28  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.10/12.28  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.10/12.28  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 12.10/12.28  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 12.10/12.28  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 12.10/12.28  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 12.10/12.28  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 12.10/12.28  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 12.10/12.28  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 12.10/12.28  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 12.10/12.28  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 12.10/12.28  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 12.10/12.28  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 12.10/12.28  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 12.10/12.28  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 12.10/12.28  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 12.10/12.28  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 12.10/12.28  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.10/12.28  fof(t151_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 12.10/12.28  fof(c_0_21, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 12.10/12.28  fof(c_0_22, plain, ![X39, X40, X41]:((v1_funct_1(X41)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_xboole_0(X40))&(v1_partfun1(X41,X39)|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_xboole_0(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 12.10/12.28  fof(c_0_23, negated_conjecture, (~v1_xboole_0(esk1_0)&(~v1_xboole_0(esk2_0)&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)))&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)))&(r1_subset_1(esk3_0,esk4_0)&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk2_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk2_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0))))&(k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])).
% 12.10/12.28  fof(c_0_24, plain, ![X36, X37, X38]:((v4_relat_1(X38,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v5_relat_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 12.10/12.28  fof(c_0_25, plain, ![X33, X34, X35]:(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 12.10/12.28  fof(c_0_26, plain, ![X42, X43]:((~v1_partfun1(X43,X42)|k1_relat_1(X43)=X42|(~v1_relat_1(X43)|~v4_relat_1(X43,X42)))&(k1_relat_1(X43)!=X42|v1_partfun1(X43,X42)|(~v1_relat_1(X43)|~v4_relat_1(X43,X42)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 12.10/12.28  cnf(c_0_27, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 12.10/12.28  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_32, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 12.10/12.28  cnf(c_0_33, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 12.10/12.28  fof(c_0_34, plain, ![X25, X26]:(~v1_relat_1(X25)|(~r1_xboole_0(X26,k1_relat_1(X25))|k7_relat_1(X25,X26)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 12.10/12.28  cnf(c_0_35, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 12.10/12.28  cnf(c_0_36, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 12.10/12.28  cnf(c_0_37, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_30])).
% 12.10/12.28  cnf(c_0_38, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_30])).
% 12.10/12.28  fof(c_0_39, plain, ![X31, X32]:((~r1_subset_1(X31,X32)|r1_xboole_0(X31,X32)|(v1_xboole_0(X31)|v1_xboole_0(X32)))&(~r1_xboole_0(X31,X32)|r1_subset_1(X31,X32)|(v1_xboole_0(X31)|v1_xboole_0(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 12.10/12.28  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk5_0,esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_43, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 12.10/12.28  cnf(c_0_44, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38])])).
% 12.10/12.28  cnf(c_0_45, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 12.10/12.28  cnf(c_0_46, negated_conjecture, (r1_subset_1(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_48, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_49, negated_conjecture, (v1_partfun1(esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_40]), c_0_41]), c_0_42])]), c_0_31])).
% 12.10/12.28  cnf(c_0_50, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_32, c_0_42])).
% 12.10/12.28  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_42])).
% 12.10/12.28  fof(c_0_52, plain, ![X29, X30]:((k7_relat_1(X30,X29)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_xboole_0(k1_relat_1(X30),X29)|k7_relat_1(X30,X29)=k1_xboole_0|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 12.10/12.28  cnf(c_0_53, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_38])])).
% 12.10/12.28  cnf(c_0_54, negated_conjecture, (r1_xboole_0(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])).
% 12.10/12.28  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk5_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_49]), c_0_50]), c_0_51])])).
% 12.10/12.28  cnf(c_0_56, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 12.10/12.28  cnf(c_0_57, negated_conjecture, (k7_relat_1(esk6_0,esk3_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 12.10/12.28  fof(c_0_58, plain, ![X27, X28]:(~v1_relat_1(X28)|r1_tarski(k1_relat_1(k7_relat_1(X28,X27)),X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 12.10/12.28  cnf(c_0_59, negated_conjecture, (k7_relat_1(esk5_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_55]), c_0_51])])).
% 12.10/12.28  cnf(c_0_60, negated_conjecture, (r1_xboole_0(esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_44]), c_0_38])])).
% 12.10/12.28  fof(c_0_61, plain, ![X44, X45, X46, X47]:(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|k2_partfun1(X44,X45,X46,X47)=k7_relat_1(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 12.10/12.28  fof(c_0_62, plain, ![X19]:(~v1_relat_1(X19)|k9_relat_1(X19,k1_relat_1(X19))=k2_relat_1(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 12.10/12.28  fof(c_0_63, plain, ![X17, X18]:(~v1_relat_1(X17)|v1_relat_1(k7_relat_1(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 12.10/12.28  fof(c_0_64, plain, ![X55, X56, X57, X58, X59, X60]:(((v1_funct_1(k1_tmap_1(X55,X56,X57,X58,X59,X60))|(v1_xboole_0(X55)|v1_xboole_0(X56)|v1_xboole_0(X57)|~m1_subset_1(X57,k1_zfmisc_1(X55))|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X55))|~v1_funct_1(X59)|~v1_funct_2(X59,X57,X56)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X56)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X56)))))&(v1_funct_2(k1_tmap_1(X55,X56,X57,X58,X59,X60),k4_subset_1(X55,X57,X58),X56)|(v1_xboole_0(X55)|v1_xboole_0(X56)|v1_xboole_0(X57)|~m1_subset_1(X57,k1_zfmisc_1(X55))|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X55))|~v1_funct_1(X59)|~v1_funct_2(X59,X57,X56)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X56)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X56))))))&(m1_subset_1(k1_tmap_1(X55,X56,X57,X58,X59,X60),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X55,X57,X58),X56)))|(v1_xboole_0(X55)|v1_xboole_0(X56)|v1_xboole_0(X57)|~m1_subset_1(X57,k1_zfmisc_1(X55))|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X55))|~v1_funct_1(X59)|~v1_funct_2(X59,X57,X56)|~m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X57,X56)))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X56)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 12.10/12.28  fof(c_0_65, plain, ![X13, X14]:(~v1_xboole_0(X13)|(~m1_subset_1(X14,k1_zfmisc_1(X13))|v1_xboole_0(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 12.10/12.28  fof(c_0_66, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 12.10/12.28  fof(c_0_67, plain, ![X15, X16]:k1_setfam_1(k2_tarski(X15,X16))=k3_xboole_0(X15,X16), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 12.10/12.28  fof(c_0_68, plain, ![X22, X23, X24]:(~v1_relat_1(X22)|(~r1_tarski(X23,X24)|k9_relat_1(k7_relat_1(X22,X24),X23)=k9_relat_1(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 12.10/12.28  cnf(c_0_69, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 12.10/12.28  cnf(c_0_70, negated_conjecture, (k7_relat_1(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 12.10/12.28  cnf(c_0_71, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 12.10/12.28  cnf(c_0_72, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 12.10/12.28  cnf(c_0_73, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 12.10/12.28  cnf(c_0_74, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 12.10/12.28  cnf(c_0_75, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 12.10/12.28  fof(c_0_76, plain, ![X48, X49, X50, X51, X52, X53, X54]:(((k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X50)=X52|X54!=k1_tmap_1(X48,X49,X50,X51,X52,X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,k4_subset_1(X48,X50,X51),X49)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49))))|k2_partfun1(X50,X49,X52,k9_subset_1(X48,X50,X51))!=k2_partfun1(X51,X49,X53,k9_subset_1(X48,X50,X51))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49))))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48)))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48)))|v1_xboole_0(X49)|v1_xboole_0(X48))&(k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X51)=X53|X54!=k1_tmap_1(X48,X49,X50,X51,X52,X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,k4_subset_1(X48,X50,X51),X49)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49))))|k2_partfun1(X50,X49,X52,k9_subset_1(X48,X50,X51))!=k2_partfun1(X51,X49,X53,k9_subset_1(X48,X50,X51))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49))))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48)))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48)))|v1_xboole_0(X49)|v1_xboole_0(X48)))&(k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X50)!=X52|k2_partfun1(k4_subset_1(X48,X50,X51),X49,X54,X51)!=X53|X54=k1_tmap_1(X48,X49,X50,X51,X52,X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,k4_subset_1(X48,X50,X51),X49)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X48,X50,X51),X49))))|k2_partfun1(X50,X49,X52,k9_subset_1(X48,X50,X51))!=k2_partfun1(X51,X49,X53,k9_subset_1(X48,X50,X51))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X49)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X49))))|(~v1_funct_1(X52)|~v1_funct_2(X52,X50,X49)|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X49))))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X48)))|(v1_xboole_0(X50)|~m1_subset_1(X50,k1_zfmisc_1(X48)))|v1_xboole_0(X49)|v1_xboole_0(X48))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 12.10/12.28  cnf(c_0_77, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 12.10/12.28  cnf(c_0_78, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 12.10/12.28  cnf(c_0_79, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 12.10/12.28  cnf(c_0_80, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 12.10/12.28  cnf(c_0_81, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 12.10/12.28  cnf(c_0_82, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 12.10/12.28  fof(c_0_83, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 12.10/12.28  cnf(c_0_84, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 12.10/12.28  cnf(c_0_85, negated_conjecture, (r1_tarski(k1_xboole_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_51])])).
% 12.10/12.28  cnf(c_0_86, negated_conjecture, (k7_relat_1(esk5_0,X1)=k2_partfun1(esk3_0,esk2_0,esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_42]), c_0_41])])).
% 12.10/12.28  cnf(c_0_87, plain, (k9_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_71])).
% 12.10/12.28  cnf(c_0_88, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_57]), c_0_38])])).
% 12.10/12.28  cnf(c_0_89, negated_conjecture, (r1_tarski(k1_xboole_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_57]), c_0_71]), c_0_38])])).
% 12.10/12.28  cnf(c_0_90, negated_conjecture, (k7_relat_1(esk6_0,X1)=k2_partfun1(esk4_0,esk2_0,esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_30]), c_0_29])])).
% 12.10/12.28  cnf(c_0_91, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 12.10/12.28  cnf(c_0_92, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_77, c_0_78])).
% 12.10/12.28  cnf(c_0_93, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_79, c_0_78])).
% 12.10/12.28  cnf(c_0_94, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_80, c_0_78])).
% 12.10/12.28  cnf(c_0_95, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 12.10/12.28  cnf(c_0_96, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_97, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 12.10/12.28  cnf(c_0_98, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 12.10/12.28  fof(c_0_99, plain, ![X20, X21]:((k9_relat_1(X21,X20)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X21),X20)|~v1_relat_1(X21))&(~r1_xboole_0(k1_relat_1(X21),X20)|k9_relat_1(X21,X20)=k1_xboole_0|~v1_relat_1(X21))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t151_relat_1])])])).
% 12.10/12.28  cnf(c_0_100, negated_conjecture, (k9_relat_1(k7_relat_1(X1,esk4_0),k1_xboole_0)=k9_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 12.10/12.28  cnf(c_0_101, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_70, c_0_86])).
% 12.10/12.28  cnf(c_0_102, plain, (k9_relat_1(k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_87, c_0_88])])).
% 12.10/12.28  cnf(c_0_103, negated_conjecture, (k9_relat_1(k7_relat_1(X1,esk3_0),k1_xboole_0)=k9_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_84, c_0_89])).
% 12.10/12.28  cnf(c_0_104, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,esk3_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_57, c_0_90])).
% 12.10/12.28  cnf(c_0_105, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_91, c_0_78])]), c_0_92]), c_0_93]), c_0_94])).
% 12.10/12.28  cnf(c_0_106, negated_conjecture, (k9_subset_1(esk1_0,X1,esk4_0)=k1_setfam_1(k2_tarski(X1,esk4_0))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 12.10/12.28  cnf(c_0_107, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_97, c_0_82])).
% 12.10/12.28  cnf(c_0_108, negated_conjecture, (k7_relat_1(esk5_0,X1)=k1_xboole_0|~r1_xboole_0(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_55]), c_0_51])])).
% 12.10/12.28  cnf(c_0_109, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k9_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_99])).
% 12.10/12.28  cnf(c_0_110, negated_conjecture, (k9_relat_1(esk5_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_86]), c_0_101]), c_0_102]), c_0_51])])).
% 12.10/12.28  cnf(c_0_111, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_76])).
% 12.10/12.28  cnf(c_0_112, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_44]), c_0_38])])).
% 12.10/12.28  cnf(c_0_113, negated_conjecture, (k9_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_90]), c_0_104]), c_0_102]), c_0_38])])).
% 12.10/12.28  cnf(c_0_114, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),X1)=X3|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk4_0)))!=k2_partfun1(esk4_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk4_0)))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_96])]), c_0_47])).
% 12.10/12.28  cnf(c_0_115, negated_conjecture, (k1_setfam_1(k2_tarski(esk3_0,esk4_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_107, c_0_54])).
% 12.10/12.28  cnf(c_0_116, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_117, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,X1)=k1_xboole_0|~r1_xboole_0(esk3_0,X1)), inference(rw,[status(thm)],[c_0_108, c_0_86])).
% 12.10/12.28  cnf(c_0_118, negated_conjecture, (r1_xboole_0(esk3_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_55]), c_0_51])])).
% 12.10/12.28  cnf(c_0_119, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_111, c_0_78])]), c_0_92]), c_0_93]), c_0_94])).
% 12.10/12.28  cnf(c_0_120, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,X1)=k1_xboole_0|~r1_xboole_0(esk4_0,X1)), inference(rw,[status(thm)],[c_0_112, c_0_90])).
% 12.10/12.28  cnf(c_0_121, negated_conjecture, (r1_xboole_0(esk4_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_113]), c_0_44]), c_0_38])])).
% 12.10/12.28  cnf(c_0_122, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk3_0)=X2|v1_xboole_0(X1)|k2_partfun1(esk3_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk4_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk4_0,X1)|~v1_funct_2(X2,esk3_0,X1)|~v1_funct_1(X3)|~v1_funct_1(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_116])]), c_0_48])).
% 12.10/12.28  cnf(c_0_123, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 12.10/12.28  cnf(c_0_124, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,X1,esk4_0),X2,k1_tmap_1(esk1_0,X2,X1,esk4_0,X3,X4),esk4_0)=X4|v1_xboole_0(X2)|v1_xboole_0(X1)|k2_partfun1(X1,X2,X3,k1_setfam_1(k2_tarski(X1,esk4_0)))!=k2_partfun1(esk4_0,X2,X4,k1_setfam_1(k2_tarski(X1,esk4_0)))|~v1_funct_2(X4,esk4_0,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X1,k1_zfmisc_1(esk1_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_106]), c_0_96])]), c_0_47])).
% 12.10/12.28  cnf(c_0_125, negated_conjecture, (k2_partfun1(esk3_0,esk2_0,esk5_0,k9_subset_1(esk1_0,esk3_0,esk4_0))!=k2_partfun1(esk4_0,esk2_0,esk6_0,k9_subset_1(esk1_0,esk3_0,esk4_0))|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 12.10/12.28  cnf(c_0_126, negated_conjecture, (k2_partfun1(esk4_0,esk2_0,esk6_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_120, c_0_121])).
% 12.10/12.28  cnf(c_0_127, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,X1),esk3_0)=esk5_0|k2_partfun1(esk4_0,esk2_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk4_0,esk2_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_122, c_0_123]), c_0_40]), c_0_41]), c_0_42])]), c_0_31])).
% 12.10/12.28  cnf(c_0_128, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),X1,k1_tmap_1(esk1_0,X1,esk3_0,esk4_0,X2,X3),esk4_0)=X3|v1_xboole_0(X1)|k2_partfun1(esk3_0,X1,X2,k1_xboole_0)!=k2_partfun1(esk4_0,X1,X3,k1_xboole_0)|~v1_funct_2(X3,esk4_0,X1)|~v1_funct_2(X2,esk3_0,X1)|~v1_funct_1(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(esk3_0,X1)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_115]), c_0_116])]), c_0_48])).
% 12.10/12.28  cnf(c_0_129, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)!=esk5_0|k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_125, c_0_106]), c_0_115]), c_0_126]), c_0_106]), c_0_115]), c_0_123])])).
% 12.10/12.28  cnf(c_0_130, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk3_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_126]), c_0_28]), c_0_29]), c_0_30])])).
% 12.10/12.28  cnf(c_0_131, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,X1,esk6_0),esk4_0)=esk6_0|k2_partfun1(esk3_0,esk2_0,X1,k1_xboole_0)!=k1_xboole_0|~v1_funct_2(X1,esk3_0,esk2_0)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_126]), c_0_28]), c_0_29]), c_0_30])]), c_0_31])).
% 12.10/12.28  cnf(c_0_132, negated_conjecture, (k2_partfun1(k4_subset_1(esk1_0,esk3_0,esk4_0),esk2_0,k1_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk5_0,esk6_0),esk4_0)!=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_129, c_0_130])])).
% 12.10/12.28  cnf(c_0_133, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_123]), c_0_40]), c_0_41]), c_0_42])]), c_0_132]), ['proof']).
% 12.10/12.28  # SZS output end CNFRefutation
% 12.10/12.28  # Proof object total steps             : 134
% 12.10/12.28  # Proof object clause steps            : 92
% 12.10/12.28  # Proof object formula steps           : 42
% 12.10/12.28  # Proof object conjectures             : 61
% 12.10/12.28  # Proof object clause conjectures      : 58
% 12.10/12.28  # Proof object formula conjectures     : 3
% 12.10/12.28  # Proof object initial clauses used    : 38
% 12.10/12.28  # Proof object initial formulas used   : 21
% 12.10/12.28  # Proof object generating inferences   : 40
% 12.10/12.28  # Proof object simplifying inferences  : 115
% 12.10/12.28  # Training examples: 0 positive, 0 negative
% 12.10/12.28  # Parsed axioms                        : 21
% 12.10/12.28  # Removed by relevancy pruning/SinE    : 0
% 12.10/12.28  # Initial clauses                      : 46
% 12.10/12.28  # Removed in clause preprocessing      : 2
% 12.10/12.28  # Initial clauses in saturation        : 44
% 12.10/12.28  # Processed clauses                    : 11332
% 12.10/12.28  # ...of these trivial                  : 1987
% 12.10/12.28  # ...subsumed                          : 799
% 12.10/12.28  # ...remaining for further processing  : 8546
% 12.10/12.28  # Other redundant clauses eliminated   : 5
% 12.10/12.28  # Clauses deleted for lack of memory   : 0
% 12.10/12.28  # Backward-subsumed                    : 0
% 12.10/12.28  # Backward-rewritten                   : 1097
% 12.10/12.28  # Generated clauses                    : 1064794
% 12.10/12.28  # ...of the previous two non-trivial   : 830267
% 12.10/12.28  # Contextual simplify-reflections      : 3249
% 12.10/12.28  # Paramodulations                      : 1064780
% 12.10/12.28  # Factorizations                       : 0
% 12.10/12.28  # Equation resolutions                 : 15
% 12.10/12.28  # Propositional unsat checks           : 0
% 12.10/12.28  #    Propositional check models        : 0
% 12.10/12.28  #    Propositional check unsatisfiable : 0
% 12.10/12.28  #    Propositional clauses             : 0
% 12.10/12.28  #    Propositional clauses after purity: 0
% 12.10/12.28  #    Propositional unsat core size     : 0
% 12.10/12.28  #    Propositional preprocessing time  : 0.000
% 12.10/12.28  #    Propositional encoding time       : 0.000
% 12.10/12.28  #    Propositional solver time         : 0.000
% 12.10/12.28  #    Success case prop preproc time    : 0.000
% 12.10/12.28  #    Success case prop encoding time   : 0.000
% 12.10/12.28  #    Success case prop solver time     : 0.000
% 12.10/12.28  # Current number of processed clauses  : 7401
% 12.10/12.28  #    Positive orientable unit clauses  : 3490
% 12.10/12.28  #    Positive unorientable unit clauses: 2
% 12.10/12.28  #    Negative unit clauses             : 5
% 12.10/12.28  #    Non-unit-clauses                  : 3904
% 12.10/12.28  # Current number of unprocessed clauses: 818595
% 12.10/12.28  # ...number of literals in the above   : 1168033
% 12.10/12.28  # Current number of archived formulas  : 0
% 12.10/12.28  # Current number of archived clauses   : 1142
% 12.10/12.28  # Clause-clause subsumption calls (NU) : 13551143
% 12.10/12.28  # Rec. Clause-clause subsumption calls : 6378197
% 12.10/12.28  # Non-unit clause-clause subsumptions  : 4046
% 12.10/12.28  # Unit Clause-clause subsumption calls : 2776024
% 12.10/12.28  # Rewrite failures with RHS unbound    : 0
% 12.10/12.28  # BW rewrite match attempts            : 944856
% 12.10/12.28  # BW rewrite match successes           : 701
% 12.10/12.28  # Condensation attempts                : 0
% 12.10/12.28  # Condensation successes               : 0
% 12.10/12.28  # Termbank termtop insertions          : 56690644
% 12.14/12.33  
% 12.14/12.33  # -------------------------------------------------
% 12.14/12.33  # User time                : 11.507 s
% 12.14/12.33  # System time              : 0.474 s
% 12.14/12.33  # Total time               : 11.981 s
% 12.14/12.33  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
