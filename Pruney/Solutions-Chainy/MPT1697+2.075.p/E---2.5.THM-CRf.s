%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:45 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 354 expanded)
%              Number of clauses        :   64 ( 128 expanded)
%              Number of leaves         :   19 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  520 (3284 expanded)
%              Number of equality atoms :   71 ( 494 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

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

fof(t187_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_xboole_0(X2,k1_relat_1(X1))
         => k7_relat_1(X1,X2) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_19,negated_conjecture,(
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

fof(c_0_20,plain,(
    ! [X40,X41,X42] :
      ( ( v1_funct_1(X42)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | v1_xboole_0(X41) )
      & ( v1_partfun1(X42,X40)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,X40,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
        | v1_xboole_0(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0)
    & ~ v1_xboole_0(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
    & ~ v1_xboole_0(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
    & r1_subset_1(esk5_0,esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk5_0,esk4_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,esk6_0,esk4_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))
    & ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
      | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
      | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_22,plain,(
    ! [X37,X38,X39] :
      ( ( v4_relat_1(X39,X37)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( v5_relat_1(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_23,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | v1_relat_1(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_24,plain,(
    ! [X31,X32] : v1_relat_1(k2_zfmisc_1(X31,X32)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_25,plain,(
    ! [X56,X57,X58,X59,X60,X61] :
      ( ( v1_funct_1(k1_tmap_1(X56,X57,X58,X59,X60,X61))
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X56))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X57)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X57)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))) )
      & ( v1_funct_2(k1_tmap_1(X56,X57,X58,X59,X60,X61),k4_subset_1(X56,X58,X59),X57)
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X56))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X57)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X57)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))) )
      & ( m1_subset_1(k1_tmap_1(X56,X57,X58,X59,X60,X61),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X56,X58,X59),X57)))
        | v1_xboole_0(X56)
        | v1_xboole_0(X57)
        | v1_xboole_0(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(X56))
        | v1_xboole_0(X59)
        | ~ m1_subset_1(X59,k1_zfmisc_1(X56))
        | ~ v1_funct_1(X60)
        | ~ v1_funct_2(X60,X58,X57)
        | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X59,X57)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_26,plain,(
    ! [X25,X26] :
      ( ~ v1_xboole_0(X25)
      | ~ m1_subset_1(X26,k1_zfmisc_1(X25))
      | v1_xboole_0(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_27,plain,(
    ! [X43,X44] :
      ( ( ~ v1_partfun1(X44,X43)
        | k1_relat_1(X44) = X43
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) )
      & ( k1_relat_1(X44) != X43
        | v1_partfun1(X44,X43)
        | ~ v1_relat_1(X44)
        | ~ v4_relat_1(X44,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_28,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_36,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55] :
      ( ( k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51) = X53
        | X55 != k1_tmap_1(X49,X50,X51,X52,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52)) != k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52) = X54
        | X55 != k1_tmap_1(X49,X50,X51,X52,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52)) != k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) )
      & ( k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51) != X53
        | k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52) != X54
        | X55 = k1_tmap_1(X49,X50,X51,X52,X53,X54)
        | ~ v1_funct_1(X55)
        | ~ v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50)))
        | k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52)) != k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))
        | ~ v1_funct_1(X54)
        | ~ v1_funct_2(X54,X52,X50)
        | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50)))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X50)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50)))
        | v1_xboole_0(X52)
        | ~ m1_subset_1(X52,k1_zfmisc_1(X49))
        | v1_xboole_0(X51)
        | ~ m1_subset_1(X51,k1_zfmisc_1(X49))
        | v1_xboole_0(X50)
        | v1_xboole_0(X49) ) ) ),
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

fof(c_0_41,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X33)
      | ~ r1_xboole_0(X34,k1_relat_1(X33))
      | k7_relat_1(X33,X34) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_42,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( v1_partfun1(esk8_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( v4_relat_1(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_35])])).

fof(c_0_46,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_xboole_0(X8)
        | ~ r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_1(X10),X10)
        | v1_xboole_0(X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_47,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r1_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,plain,
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

cnf(c_0_52,plain,
    ( m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))
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
    inference(csr,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,plain,
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

cnf(c_0_54,plain,
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

fof(c_0_55,plain,(
    ! [X45,X46,X47,X48] :
      ( ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k2_partfun1(X45,X46,X47,X48) = k7_relat_1(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_56,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])])).

fof(c_0_58,plain,(
    ! [X14,X15] :
      ( ~ r1_xboole_0(X14,X15)
      | r1_xboole_0(X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

cnf(c_0_59,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_60,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_48]),c_0_49]),c_0_50])]),c_0_32])).

cnf(c_0_62,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_50]),c_0_35])])).

cnf(c_0_64,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_65,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_51,c_0_38])]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_70,plain,
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

cnf(c_0_71,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_72,negated_conjecture,
    ( k7_relat_1(esk8_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_45])])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_61]),c_0_62]),c_0_63])])).

cnf(c_0_76,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))
    | k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0) != esk7_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_48]),c_0_29]),c_0_49]),c_0_30]),c_0_50]),c_0_31]),c_0_66]),c_0_67])]),c_0_32]),c_0_68]),c_0_69])).

cnf(c_0_77,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_70,c_0_38])]),c_0_52]),c_0_53]),c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,X3) = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_xboole_0(X3,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_30])])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_75]),c_0_63])])).

fof(c_0_81,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X22))
      | k9_subset_1(X22,X23,X24) = k3_xboole_0(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_82,plain,(
    ! [X27,X28] : k1_setfam_1(k2_tarski(X27,X28)) = k3_xboole_0(X27,X28) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_83,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k3_xboole_0(X12,X13) = k1_xboole_0 )
      & ( k3_xboole_0(X12,X13) != k1_xboole_0
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_29]),c_0_48]),c_0_30]),c_0_49]),c_0_31]),c_0_50]),c_0_66]),c_0_67])]),c_0_32]),c_0_68]),c_0_69])).

cnf(c_0_85,negated_conjecture,
    ( k2_partfun1(X1,X2,esk8_0,X3) = k1_xboole_0
    | ~ m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( k2_partfun1(X1,X2,esk7_0,X3) = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_xboole_0(X3,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_80]),c_0_49])])).

cnf(c_0_87,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_88,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

cnf(c_0_89,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

fof(c_0_90,plain,(
    ! [X35,X36] :
      ( ( ~ r1_subset_1(X35,X36)
        | r1_xboole_0(X35,X36)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) )
      & ( ~ r1_xboole_0(X35,X36)
        | r1_subset_1(X35,X36)
        | v1_xboole_0(X35)
        | v1_xboole_0(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_91,negated_conjecture,
    ( k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0)) != k1_xboole_0
    | ~ v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_31])])).

cnf(c_0_92,negated_conjecture,
    ( k2_partfun1(X1,X2,esk7_0,X3) = k1_xboole_0
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_86,c_0_79])).

cnf(c_0_93,plain,
    ( k9_subset_1(X2,X3,X1) = k1_setfam_1(k2_tarski(X3,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_94,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_89,c_0_88])).

cnf(c_0_95,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( r1_subset_1(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_97,negated_conjecture,
    ( ~ v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_50])])).

cnf(c_0_98,plain,
    ( k9_subset_1(X1,X2,X3) = k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_99,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_100,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_69]),c_0_68])).

cnf(c_0_101,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_99]),c_0_66]),c_0_100])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.31  % Computer   : n017.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 15:37:01 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  # Version: 2.5pre002
% 0.17/0.31  # No SInE strategy applied
% 0.17/0.31  # Trying AutoSched0 for 299 seconds
% 4.44/4.64  # AutoSched0-Mode selected heuristic G_____0021_C18_F1_SE_CS_SP_S0Y
% 4.44/4.64  # and selection function SelectMaxLComplexAvoidPosPred.
% 4.44/4.64  #
% 4.44/4.64  # Preprocessing time       : 0.041 s
% 4.44/4.64  
% 4.44/4.64  # Proof found!
% 4.44/4.64  # SZS status Theorem
% 4.44/4.64  # SZS output start CNFRefutation
% 4.44/4.64  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 4.44/4.64  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.44/4.64  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.44/4.64  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.44/4.64  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.44/4.64  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 4.44/4.64  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.44/4.64  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.44/4.64  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 4.44/4.64  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 4.44/4.64  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.44/4.64  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.44/4.64  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.44/4.64  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.44/4.64  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.44/4.64  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.44/4.64  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.44/4.64  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 4.44/4.64  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.44/4.64  fof(c_0_19, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 4.44/4.64  fof(c_0_20, plain, ![X40, X41, X42]:((v1_funct_1(X42)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))&(v1_partfun1(X42,X40)|(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|v1_xboole_0(X41))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 4.44/4.64  fof(c_0_21, negated_conjecture, (~v1_xboole_0(esk3_0)&(~v1_xboole_0(esk4_0)&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0)))&((~v1_xboole_0(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)))&(r1_subset_1(esk5_0,esk6_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk4_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk4_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0))))&(k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).
% 4.44/4.64  fof(c_0_22, plain, ![X37, X38, X39]:((v4_relat_1(X39,X37)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(v5_relat_1(X39,X38)|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 4.44/4.64  fof(c_0_23, plain, ![X29, X30]:(~v1_relat_1(X29)|(~m1_subset_1(X30,k1_zfmisc_1(X29))|v1_relat_1(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 4.44/4.64  fof(c_0_24, plain, ![X31, X32]:v1_relat_1(k2_zfmisc_1(X31,X32)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 4.44/4.64  fof(c_0_25, plain, ![X56, X57, X58, X59, X60, X61]:(((v1_funct_1(k1_tmap_1(X56,X57,X58,X59,X60,X61))|(v1_xboole_0(X56)|v1_xboole_0(X57)|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X56))|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X56))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X57)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X57)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57)))))&(v1_funct_2(k1_tmap_1(X56,X57,X58,X59,X60,X61),k4_subset_1(X56,X58,X59),X57)|(v1_xboole_0(X56)|v1_xboole_0(X57)|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X56))|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X56))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X57)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X57)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57))))))&(m1_subset_1(k1_tmap_1(X56,X57,X58,X59,X60,X61),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X56,X58,X59),X57)))|(v1_xboole_0(X56)|v1_xboole_0(X57)|v1_xboole_0(X58)|~m1_subset_1(X58,k1_zfmisc_1(X56))|v1_xboole_0(X59)|~m1_subset_1(X59,k1_zfmisc_1(X56))|~v1_funct_1(X60)|~v1_funct_2(X60,X58,X57)|~m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(X58,X57)))|~v1_funct_1(X61)|~v1_funct_2(X61,X59,X57)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X57)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 4.44/4.64  fof(c_0_26, plain, ![X25, X26]:(~v1_xboole_0(X25)|(~m1_subset_1(X26,k1_zfmisc_1(X25))|v1_xboole_0(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 4.44/4.64  fof(c_0_27, plain, ![X43, X44]:((~v1_partfun1(X44,X43)|k1_relat_1(X44)=X43|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))&(k1_relat_1(X44)!=X43|v1_partfun1(X44,X43)|(~v1_relat_1(X44)|~v4_relat_1(X44,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 4.44/4.64  cnf(c_0_28, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 4.44/4.64  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_32, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_33, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 4.44/4.64  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 4.44/4.64  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 4.44/4.64  fof(c_0_36, plain, ![X49, X50, X51, X52, X53, X54, X55]:(((k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51)=X53|X55!=k1_tmap_1(X49,X50,X51,X52,X53,X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50))))|k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52))!=k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49)))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49)))|v1_xboole_0(X50)|v1_xboole_0(X49))&(k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52)=X54|X55!=k1_tmap_1(X49,X50,X51,X52,X53,X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50))))|k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52))!=k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49)))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49)))|v1_xboole_0(X50)|v1_xboole_0(X49)))&(k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X51)!=X53|k2_partfun1(k4_subset_1(X49,X51,X52),X50,X55,X52)!=X54|X55=k1_tmap_1(X49,X50,X51,X52,X53,X54)|(~v1_funct_1(X55)|~v1_funct_2(X55,k4_subset_1(X49,X51,X52),X50)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X49,X51,X52),X50))))|k2_partfun1(X51,X50,X53,k9_subset_1(X49,X51,X52))!=k2_partfun1(X52,X50,X54,k9_subset_1(X49,X51,X52))|(~v1_funct_1(X54)|~v1_funct_2(X54,X52,X50)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X50))))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X50)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X50))))|(v1_xboole_0(X52)|~m1_subset_1(X52,k1_zfmisc_1(X49)))|(v1_xboole_0(X51)|~m1_subset_1(X51,k1_zfmisc_1(X49)))|v1_xboole_0(X50)|v1_xboole_0(X49))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 4.44/4.64  cnf(c_0_37, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.44/4.64  cnf(c_0_38, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 4.44/4.64  cnf(c_0_39, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.44/4.64  cnf(c_0_40, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 4.44/4.64  fof(c_0_41, plain, ![X33, X34]:(~v1_relat_1(X33)|(~r1_xboole_0(X34,k1_relat_1(X33))|k7_relat_1(X33,X34)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 4.44/4.64  cnf(c_0_42, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 4.44/4.64  cnf(c_0_43, negated_conjecture, (v1_partfun1(esk8_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])]), c_0_32])).
% 4.44/4.64  cnf(c_0_44, negated_conjecture, (v4_relat_1(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_33, c_0_31])).
% 4.44/4.64  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_35])])).
% 4.44/4.64  fof(c_0_46, plain, ![X8, X9, X10]:((~v1_xboole_0(X8)|~r2_hidden(X9,X8))&(r2_hidden(esk1_1(X10),X10)|v1_xboole_0(X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 4.44/4.64  fof(c_0_47, plain, ![X16, X17, X19, X20, X21]:(((r2_hidden(esk2_2(X16,X17),X16)|r1_xboole_0(X16,X17))&(r2_hidden(esk2_2(X16,X17),X17)|r1_xboole_0(X16,X17)))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|~r1_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 4.44/4.64  cnf(c_0_48, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_51, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.44/4.64  cnf(c_0_52, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_37, c_0_38])).
% 4.44/4.64  cnf(c_0_53, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_39, c_0_38])).
% 4.44/4.64  cnf(c_0_54, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_40, c_0_38])).
% 4.44/4.64  fof(c_0_55, plain, ![X45, X46, X47, X48]:(~v1_funct_1(X47)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k2_partfun1(X45,X46,X47,X48)=k7_relat_1(X47,X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 4.44/4.64  cnf(c_0_56, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 4.44/4.64  cnf(c_0_57, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])])).
% 4.44/4.64  fof(c_0_58, plain, ![X14, X15]:(~r1_xboole_0(X14,X15)|r1_xboole_0(X15,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 4.44/4.64  cnf(c_0_59, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 4.44/4.64  cnf(c_0_60, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 4.44/4.64  cnf(c_0_61, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_48]), c_0_49]), c_0_50])]), c_0_32])).
% 4.44/4.64  cnf(c_0_62, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_33, c_0_50])).
% 4.44/4.64  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_50]), c_0_35])])).
% 4.44/4.64  cnf(c_0_64, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk6_0)!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_65, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_51, c_0_38])]), c_0_52]), c_0_53]), c_0_54])).
% 4.44/4.64  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_69, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_70, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 4.44/4.64  cnf(c_0_71, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 4.44/4.64  cnf(c_0_72, negated_conjecture, (k7_relat_1(esk8_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_45])])).
% 4.44/4.64  cnf(c_0_73, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 4.44/4.64  cnf(c_0_74, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 4.44/4.64  cnf(c_0_75, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_61]), c_0_62]), c_0_63])])).
% 4.44/4.64  cnf(c_0_76, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))|k2_partfun1(k4_subset_1(esk3_0,esk5_0,esk6_0),esk4_0,k1_tmap_1(esk3_0,esk4_0,esk5_0,esk6_0,esk7_0,esk8_0),esk5_0)!=esk7_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_48]), c_0_29]), c_0_49]), c_0_30]), c_0_50]), c_0_31]), c_0_66]), c_0_67])]), c_0_32]), c_0_68]), c_0_69])).
% 4.44/4.64  cnf(c_0_77, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_70, c_0_38])]), c_0_52]), c_0_53]), c_0_54])).
% 4.44/4.64  cnf(c_0_78, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,X3)=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_xboole_0(X3,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_30])])).
% 4.44/4.64  cnf(c_0_79, plain, (r1_xboole_0(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 4.44/4.64  cnf(c_0_80, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_75]), c_0_63])])).
% 4.44/4.64  fof(c_0_81, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(X22))|k9_subset_1(X22,X23,X24)=k3_xboole_0(X23,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 4.44/4.64  fof(c_0_82, plain, ![X27, X28]:k1_setfam_1(k2_tarski(X27,X28))=k3_xboole_0(X27,X28), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 4.44/4.64  fof(c_0_83, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k3_xboole_0(X12,X13)=k1_xboole_0)&(k3_xboole_0(X12,X13)!=k1_xboole_0|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 4.44/4.64  cnf(c_0_84, negated_conjecture, (k2_partfun1(esk6_0,esk4_0,esk8_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_29]), c_0_48]), c_0_30]), c_0_49]), c_0_31]), c_0_50]), c_0_66]), c_0_67])]), c_0_32]), c_0_68]), c_0_69])).
% 4.44/4.64  cnf(c_0_85, negated_conjecture, (k2_partfun1(X1,X2,esk8_0,X3)=k1_xboole_0|~m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 4.44/4.64  cnf(c_0_86, negated_conjecture, (k2_partfun1(X1,X2,esk7_0,X3)=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~r1_xboole_0(X3,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_80]), c_0_49])])).
% 4.44/4.64  cnf(c_0_87, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_81])).
% 4.44/4.64  cnf(c_0_88, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_82])).
% 4.44/4.64  cnf(c_0_89, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_83])).
% 4.44/4.64  fof(c_0_90, plain, ![X35, X36]:((~r1_subset_1(X35,X36)|r1_xboole_0(X35,X36)|(v1_xboole_0(X35)|v1_xboole_0(X36)))&(~r1_xboole_0(X35,X36)|r1_subset_1(X35,X36)|(v1_xboole_0(X35)|v1_xboole_0(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 4.44/4.64  cnf(c_0_91, negated_conjecture, (k2_partfun1(esk5_0,esk4_0,esk7_0,k9_subset_1(esk3_0,esk5_0,esk6_0))!=k1_xboole_0|~v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_31])])).
% 4.44/4.64  cnf(c_0_92, negated_conjecture, (k2_partfun1(X1,X2,esk7_0,X3)=k1_xboole_0|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_86, c_0_79])).
% 4.44/4.64  cnf(c_0_93, plain, (k9_subset_1(X2,X3,X1)=k1_setfam_1(k2_tarski(X3,X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_87, c_0_88])).
% 4.44/4.64  cnf(c_0_94, plain, (k1_setfam_1(k2_tarski(X1,X2))=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_89, c_0_88])).
% 4.44/4.64  cnf(c_0_95, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 4.44/4.64  cnf(c_0_96, negated_conjecture, (r1_subset_1(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 4.44/4.64  cnf(c_0_97, negated_conjecture, (~v1_xboole_0(k9_subset_1(esk3_0,esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_50])])).
% 4.44/4.64  cnf(c_0_98, plain, (k9_subset_1(X1,X2,X3)=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_93, c_0_94])).
% 4.44/4.64  cnf(c_0_99, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 4.44/4.64  cnf(c_0_100, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_96]), c_0_69]), c_0_68])).
% 4.44/4.64  cnf(c_0_101, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_99]), c_0_66]), c_0_100])]), ['proof']).
% 4.44/4.64  # SZS output end CNFRefutation
% 4.44/4.64  # Proof object total steps             : 102
% 4.44/4.64  # Proof object clause steps            : 64
% 4.44/4.64  # Proof object formula steps           : 38
% 4.44/4.64  # Proof object conjectures             : 36
% 4.44/4.64  # Proof object clause conjectures      : 33
% 4.44/4.64  # Proof object formula conjectures     : 3
% 4.44/4.64  # Proof object initial clauses used    : 34
% 4.44/4.64  # Proof object initial formulas used   : 19
% 4.44/4.64  # Proof object generating inferences   : 23
% 4.44/4.64  # Proof object simplifying inferences  : 75
% 4.44/4.64  # Training examples: 0 positive, 0 negative
% 4.44/4.64  # Parsed axioms                        : 19
% 4.44/4.64  # Removed by relevancy pruning/SinE    : 0
% 4.44/4.64  # Initial clauses                      : 44
% 4.44/4.64  # Removed in clause preprocessing      : 2
% 4.44/4.64  # Initial clauses in saturation        : 42
% 4.44/4.64  # Processed clauses                    : 14082
% 4.44/4.64  # ...of these trivial                  : 0
% 4.44/4.64  # ...subsumed                          : 10823
% 4.44/4.64  # ...remaining for further processing  : 3259
% 4.44/4.64  # Other redundant clauses eliminated   : 14781
% 4.44/4.64  # Clauses deleted for lack of memory   : 0
% 4.44/4.64  # Backward-subsumed                    : 827
% 4.44/4.64  # Backward-rewritten                   : 2
% 4.44/4.64  # Generated clauses                    : 100829
% 4.44/4.64  # ...of the previous two non-trivial   : 49794
% 4.44/4.64  # Contextual simplify-reflections      : 163
% 4.44/4.64  # Paramodulations                      : 85998
% 4.44/4.64  # Factorizations                       : 0
% 4.44/4.64  # Equation resolutions                 : 14832
% 4.44/4.64  # Propositional unsat checks           : 0
% 4.44/4.64  #    Propositional check models        : 0
% 4.44/4.64  #    Propositional check unsatisfiable : 0
% 4.44/4.64  #    Propositional clauses             : 0
% 4.44/4.64  #    Propositional clauses after purity: 0
% 4.44/4.64  #    Propositional unsat core size     : 0
% 4.44/4.64  #    Propositional preprocessing time  : 0.000
% 4.44/4.64  #    Propositional encoding time       : 0.000
% 4.44/4.64  #    Propositional solver time         : 0.000
% 4.44/4.64  #    Success case prop preproc time    : 0.000
% 4.44/4.64  #    Success case prop encoding time   : 0.000
% 4.44/4.64  #    Success case prop solver time     : 0.000
% 4.44/4.64  # Current number of processed clauses  : 2426
% 4.44/4.64  #    Positive orientable unit clauses  : 25
% 4.44/4.64  #    Positive unorientable unit clauses: 0
% 4.44/4.64  #    Negative unit clauses             : 7
% 4.44/4.64  #    Non-unit-clauses                  : 2394
% 4.44/4.64  # Current number of unprocessed clauses: 35152
% 4.44/4.64  # ...number of literals in the above   : 883075
% 4.44/4.64  # Current number of archived formulas  : 0
% 4.44/4.64  # Current number of archived clauses   : 830
% 4.44/4.64  # Clause-clause subsumption calls (NU) : 3457174
% 4.44/4.64  # Rec. Clause-clause subsumption calls : 85729
% 4.44/4.64  # Non-unit clause-clause subsumptions  : 11369
% 4.44/4.64  # Unit Clause-clause subsumption calls : 482
% 4.44/4.64  # Rewrite failures with RHS unbound    : 0
% 4.44/4.64  # BW rewrite match attempts            : 2
% 4.44/4.64  # BW rewrite match successes           : 2
% 4.44/4.64  # Condensation attempts                : 0
% 4.44/4.64  # Condensation successes               : 0
% 4.44/4.64  # Termbank termtop insertions          : 9064516
% 4.44/4.65  
% 4.44/4.65  # -------------------------------------------------
% 4.44/4.65  # User time                : 4.288 s
% 4.44/4.65  # System time              : 0.044 s
% 4.44/4.65  # Total time               : 4.332 s
% 4.44/4.65  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
