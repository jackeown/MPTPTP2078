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
% DateTime   : Thu Dec  3 11:16:38 EST 2020

% Result     : Theorem 0.39s
% Output     : CNFRefutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 672 expanded)
%              Number of clauses        :   82 ( 252 expanded)
%              Number of leaves         :   17 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  575 (5302 expanded)
%              Number of equality atoms :  100 ( 840 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   55 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

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

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(rc1_yellow_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v4_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_partfun1(X2,X1)
      & v1_yellow_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_yellow_1)).

fof(t134_pboole,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v4_relat_1(X1,k1_xboole_0)
        & v1_funct_1(X1)
        & v1_partfun1(X1,k1_xboole_0) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_pboole)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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

fof(t90_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k1_relat_1(k7_relat_1(X2,X1)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

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

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(c_0_17,plain,(
    ! [X45,X46,X47,X48,X49,X50,X51] :
      ( ( k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47) = X49
        | X51 != k1_tmap_1(X45,X46,X47,X48,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46)))
        | k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48)) != k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X46)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48) = X50
        | X51 != k1_tmap_1(X45,X46,X47,X48,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46)))
        | k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48)) != k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X46)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) )
      & ( k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47) != X49
        | k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48) != X50
        | X51 = k1_tmap_1(X45,X46,X47,X48,X49,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46)))
        | k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48)) != k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))
        | ~ v1_funct_1(X50)
        | ~ v1_funct_2(X50,X48,X46)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46)))
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,X47,X46)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46)))
        | v1_xboole_0(X48)
        | ~ m1_subset_1(X48,k1_zfmisc_1(X45))
        | v1_xboole_0(X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | v1_xboole_0(X46)
        | v1_xboole_0(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).

fof(c_0_18,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(X14))
      | v1_xboole_0(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

fof(c_0_19,plain,(
    ! [X52,X53,X54,X55,X56,X57] :
      ( ( v1_funct_1(k1_tmap_1(X52,X53,X54,X55,X56,X57))
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))) )
      & ( v1_funct_2(k1_tmap_1(X52,X53,X54,X55,X56,X57),k4_subset_1(X52,X54,X55),X53)
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))) )
      & ( m1_subset_1(k1_tmap_1(X52,X53,X54,X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))
        | v1_xboole_0(X52)
        | v1_xboole_0(X53)
        | v1_xboole_0(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X52))
        | v1_xboole_0(X55)
        | ~ m1_subset_1(X55,k1_zfmisc_1(X52))
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X53)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X55,X53)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).

fof(c_0_20,negated_conjecture,(
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

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_27,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3) = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))
    | X5 != k1_tmap_1(X1,X4,X2,X3,X7,X6)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ v1_funct_2(X7,X2,X4)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ v1_funct_1(X7)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
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
    inference(csr,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_29,plain,
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
    inference(csr,[status(thm)],[c_0_24,c_0_22])).

cnf(c_0_30,plain,
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
    inference(csr,[status(thm)],[c_0_25,c_0_22])).

cnf(c_0_31,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_32,plain,(
    ! [X36,X37] :
      ( ( ~ v1_partfun1(X37,X36)
        | k1_relat_1(X37) = X36
        | ~ v1_relat_1(X37)
        | ~ v4_relat_1(X37,X36) )
      & ( k1_relat_1(X37) != X36
        | v1_partfun1(X37,X36)
        | ~ v1_relat_1(X37)
        | ~ v4_relat_1(X37,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

fof(c_0_33,plain,(
    ! [X42] :
      ( v1_relat_1(esk1_1(X42))
      & v4_relat_1(esk1_1(X42),X42)
      & v1_funct_1(esk1_1(X42))
      & v1_partfun1(esk1_1(X42),X42)
      & v1_yellow_1(esk1_1(X42)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_yellow_1])])).

fof(c_0_34,plain,(
    ! [X44] :
      ( ~ v1_relat_1(X44)
      | ~ v4_relat_1(X44,k1_xboole_0)
      | ~ v1_funct_1(X44)
      | ~ v1_partfun1(X44,k1_xboole_0)
      | X44 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_pboole])])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_48,plain,
    ( k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2) = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3)) != k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))
    | X5 != k1_tmap_1(X1,X4,X2,X3,X6,X7)
    | ~ v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)
    | ~ v1_funct_2(X7,X3,X4)
    | ~ v1_funct_2(X6,X2,X4)
    | ~ v1_funct_1(X7)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(csr,[status(thm)],[c_0_31,c_0_22])).

fof(c_0_49,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ v1_funct_1(X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k2_partfun1(X38,X39,X40,X41) = k7_relat_1(X40,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_50,plain,(
    ! [X33,X34,X35] :
      ( ( v1_funct_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | v1_xboole_0(X34) )
      & ( v1_partfun1(X35,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_51,plain,(
    ! [X30,X31,X32] :
      ( ( v4_relat_1(X32,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( v5_relat_1(X32,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_52,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_relat_1(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_53,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X24)
      | k1_relat_1(k7_relat_1(X24,X23)) = k3_xboole_0(k1_relat_1(X24),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).

cnf(c_0_54,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,plain,
    ( v1_partfun1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,plain,
    ( v4_relat_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,plain,
    ( v1_relat_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_58,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ r1_xboole_0(X20,k1_relat_1(X19))
      | k7_relat_1(X19,X20) = k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_partfun1(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_60,plain,
    ( v1_funct_1(esk1_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0) != esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_62,plain,
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
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_63,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_67,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = k3_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_68,plain,
    ( k1_relat_1(esk1_1(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_57])])).

cnf(c_0_69,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_70,plain,
    ( esk1_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_55]),c_0_60]),c_0_56]),c_0_57])])).

fof(c_0_71,plain,(
    ! [X25,X26] :
      ( ( ~ r1_subset_1(X25,X26)
        | r1_xboole_0(X25,X26)
        | v1_xboole_0(X25)
        | v1_xboole_0(X26) )
      & ( ~ r1_xboole_0(X25,X26)
        | r1_subset_1(X25,X26)
        | v1_xboole_0(X25)
        | v1_xboole_0(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_72,negated_conjecture,
    ( k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_38]),c_0_37]),c_0_40]),c_0_39]),c_0_42]),c_0_41]),c_0_43]),c_0_44])]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_73,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_63])).

fof(c_0_74,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X10))
      | k9_subset_1(X10,X11,X12) = k3_xboole_0(X11,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_75,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X22)
      | k7_relat_1(X22,X21) = k7_relat_1(X22,k3_xboole_0(k1_relat_1(X22),X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).

cnf(c_0_76,negated_conjecture,
    ( v1_partfun1(esk7_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_42]),c_0_38]),c_0_40])]),c_0_45])).

cnf(c_0_77,negated_conjecture,
    ( v4_relat_1(esk7_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_42])).

cnf(c_0_78,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_42])).

cnf(c_0_79,plain,
    ( k1_relat_1(k7_relat_1(esk1_1(X1),X2)) = k3_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_57])])).

cnf(c_0_80,plain,
    ( k7_relat_1(esk1_1(X1),X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_57])])).

cnf(c_0_81,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_70])).

cnf(c_0_82,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( r1_subset_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( k2_partfun1(X1,X2,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_40]),c_0_42])])).

cnf(c_0_85,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_86,plain,
    ( k7_relat_1(X1,X2) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_76]),c_0_77]),c_0_78])])).

cnf(c_0_88,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X2,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_47]),c_0_46])).

cnf(c_0_90,negated_conjecture,
    ( v1_partfun1(esk6_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_37]),c_0_39])]),c_0_45])).

cnf(c_0_91,negated_conjecture,
    ( v4_relat_1(esk6_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_41])).

cnf(c_0_92,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_41])).

cnf(c_0_93,negated_conjecture,
    ( k7_relat_1(esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0)) != k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_63]),c_0_40])])).

cnf(c_0_94,plain,
    ( k9_subset_1(X1,X2,X3) = k9_subset_1(X4,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_85])).

fof(c_0_95,plain,(
    ! [X8,X9] :
      ( ( ~ r1_xboole_0(X8,X9)
        | k3_xboole_0(X8,X9) = k1_xboole_0 )
      & ( k3_xboole_0(X8,X9) != k1_xboole_0
        | r1_xboole_0(X8,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_96,negated_conjecture,
    ( k7_relat_1(esk7_0,k3_xboole_0(esk5_0,X1)) = k7_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_78])])).

cnf(c_0_97,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk4_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_88,c_0_89])).

cnf(c_0_98,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_90]),c_0_91]),c_0_92])])).

cnf(c_0_99,negated_conjecture,
    ( k7_relat_1(esk7_0,k9_subset_1(X1,esk4_0,esk5_0)) != k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(X1,esk4_0,esk5_0))
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_43])])).

cnf(c_0_100,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( k7_relat_1(esk7_0,esk4_0) = k7_relat_1(esk7_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_102,negated_conjecture,
    ( k7_relat_1(esk7_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_87]),c_0_78])])).

cnf(c_0_103,plain,
    ( k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2))) = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_67])).

cnf(c_0_104,negated_conjecture,
    ( k7_relat_1(esk6_0,X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_98]),c_0_92])])).

cnf(c_0_105,negated_conjecture,
    ( k7_relat_1(esk7_0,k9_subset_1(X1,esk4_0,esk5_0)) != k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(X1,esk4_0,esk5_0))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_42])).

cnf(c_0_106,negated_conjecture,
    ( k3_xboole_0(esk4_0,esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_100,c_0_89])).

cnf(c_0_107,negated_conjecture,
    ( k7_relat_1(esk7_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_89])])).

cnf(c_0_108,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0
    | ~ r1_xboole_0(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_81]),c_0_92])])).

cnf(c_0_109,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_110,negated_conjecture,
    ( k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_85]),c_0_106]),c_0_107]),c_0_106])).

cnf(c_0_111,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(X1,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_108,c_0_109])).

cnf(c_0_112,negated_conjecture,
    ( k2_partfun1(X1,X2,esk6_0,k1_xboole_0) != k1_xboole_0
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_73]),c_0_39]),c_0_41])])).

cnf(c_0_113,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_111,c_0_97])).

cnf(c_0_114,negated_conjecture,
    ( ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_63]),c_0_113]),c_0_39])])).

cnf(c_0_115,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_41])).

cnf(c_0_116,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_43,c_0_115]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.39/0.56  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.39/0.56  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.39/0.56  #
% 0.39/0.56  # Preprocessing time       : 0.067 s
% 0.39/0.56  
% 0.39/0.56  # Proof found!
% 0.39/0.56  # SZS status Theorem
% 0.39/0.56  # SZS output start CNFRefutation
% 0.39/0.56  fof(d1_tmap_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,k4_subset_1(X1,X3,X4),X2))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))=>(X7=k1_tmap_1(X1,X2,X3,X4,X5,X6)<=>(k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X3)=X5&k2_partfun1(k4_subset_1(X1,X3,X4),X2,X7,X4)=X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tmap_1)).
% 0.39/0.56  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.39/0.56  fof(dt_k1_tmap_1, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((((((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))&~(v1_xboole_0(X3)))&m1_subset_1(X3,k1_zfmisc_1(X1)))&~(v1_xboole_0(X4)))&m1_subset_1(X4,k1_zfmisc_1(X1)))&v1_funct_1(X5))&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))&v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2))&m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tmap_1)).
% 0.39/0.56  fof(t6_tmap_1, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tmap_1)).
% 0.39/0.56  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.39/0.56  fof(rc1_yellow_1, axiom, ![X1]:?[X2]:((((v1_relat_1(X2)&v4_relat_1(X2,X1))&v1_funct_1(X2))&v1_partfun1(X2,X1))&v1_yellow_1(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_yellow_1)).
% 0.39/0.56  fof(t134_pboole, axiom, ![X1]:((((v1_relat_1(X1)&v4_relat_1(X1,k1_xboole_0))&v1_funct_1(X1))&v1_partfun1(X1,k1_xboole_0))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t134_pboole)).
% 0.39/0.56  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.39/0.56  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.39/0.56  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.39/0.56  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.39/0.56  fof(t90_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k1_relat_1(k7_relat_1(X2,X1))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 0.39/0.56  fof(t187_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_xboole_0(X2,k1_relat_1(X1))=>k7_relat_1(X1,X2)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 0.39/0.56  fof(redefinition_r1_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&~(v1_xboole_0(X2)))=>(r1_subset_1(X1,X2)<=>r1_xboole_0(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_subset_1)).
% 0.39/0.56  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 0.39/0.56  fof(t192_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k7_relat_1(X2,X1)=k7_relat_1(X2,k3_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 0.39/0.56  fof(d7_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k3_xboole_0(X1,X2)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 0.39/0.56  fof(c_0_17, plain, ![X45, X46, X47, X48, X49, X50, X51]:(((k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47)=X49|X51!=k1_tmap_1(X45,X46,X47,X48,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46))))|k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48))!=k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X46)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X45)))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X45)))|v1_xboole_0(X46)|v1_xboole_0(X45))&(k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48)=X50|X51!=k1_tmap_1(X45,X46,X47,X48,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46))))|k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48))!=k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X46)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X45)))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X45)))|v1_xboole_0(X46)|v1_xboole_0(X45)))&(k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X47)!=X49|k2_partfun1(k4_subset_1(X45,X47,X48),X46,X51,X48)!=X50|X51=k1_tmap_1(X45,X46,X47,X48,X49,X50)|(~v1_funct_1(X51)|~v1_funct_2(X51,k4_subset_1(X45,X47,X48),X46)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X45,X47,X48),X46))))|k2_partfun1(X47,X46,X49,k9_subset_1(X45,X47,X48))!=k2_partfun1(X48,X46,X50,k9_subset_1(X45,X47,X48))|(~v1_funct_1(X50)|~v1_funct_2(X50,X48,X46)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X46))))|(~v1_funct_1(X49)|~v1_funct_2(X49,X47,X46)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X46))))|(v1_xboole_0(X48)|~m1_subset_1(X48,k1_zfmisc_1(X45)))|(v1_xboole_0(X47)|~m1_subset_1(X47,k1_zfmisc_1(X45)))|v1_xboole_0(X46)|v1_xboole_0(X45))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tmap_1])])])])])).
% 0.39/0.56  fof(c_0_18, plain, ![X14, X15]:(~v1_xboole_0(X14)|(~m1_subset_1(X15,k1_zfmisc_1(X14))|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.39/0.56  fof(c_0_19, plain, ![X52, X53, X54, X55, X56, X57]:(((v1_funct_1(k1_tmap_1(X52,X53,X54,X55,X56,X57))|(v1_xboole_0(X52)|v1_xboole_0(X53)|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))))&(v1_funct_2(k1_tmap_1(X52,X53,X54,X55,X56,X57),k4_subset_1(X52,X54,X55),X53)|(v1_xboole_0(X52)|v1_xboole_0(X53)|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53))))))&(m1_subset_1(k1_tmap_1(X52,X53,X54,X55,X56,X57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X52,X54,X55),X53)))|(v1_xboole_0(X52)|v1_xboole_0(X53)|v1_xboole_0(X54)|~m1_subset_1(X54,k1_zfmisc_1(X52))|v1_xboole_0(X55)|~m1_subset_1(X55,k1_zfmisc_1(X52))|~v1_funct_1(X56)|~v1_funct_2(X56,X54,X53)|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X53)))|~v1_funct_1(X57)|~v1_funct_2(X57,X55,X53)|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X53)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tmap_1])])])])).
% 0.39/0.56  fof(c_0_20, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:((~(v1_xboole_0(X3))&m1_subset_1(X3,k1_zfmisc_1(X1)))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>(r1_subset_1(X3,X4)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X3,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,X4,X2))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>((k2_partfun1(X3,X2,X5,k9_subset_1(X1,X3,X4))=k2_partfun1(X4,X2,X6,k9_subset_1(X1,X3,X4))&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X3)=X5)&k2_partfun1(k4_subset_1(X1,X3,X4),X2,k1_tmap_1(X1,X2,X3,X4,X5,X6),X4)=X6))))))))), inference(assume_negation,[status(cth)],[t6_tmap_1])).
% 0.39/0.56  cnf(c_0_21, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X7)|~v1_funct_2(X7,X2,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  cnf(c_0_22, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.39/0.56  cnf(c_0_23, plain, (m1_subset_1(k1_tmap_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X3,X4),X2)))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.56  cnf(c_0_24, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.56  cnf(c_0_25, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,X3,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X4,X2)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.39/0.56  fof(c_0_26, negated_conjecture, (~v1_xboole_0(esk2_0)&(~v1_xboole_0(esk3_0)&((~v1_xboole_0(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0)))&((~v1_xboole_0(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0)))&(r1_subset_1(esk4_0,esk5_0)&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk3_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk3_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0))))&(k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.39/0.56  cnf(c_0_27, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X3)=X6|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|k2_partfun1(X2,X4,X7,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|X5!=k1_tmap_1(X1,X4,X2,X3,X7,X6)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~v1_funct_2(X7,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X7)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.39/0.56  cnf(c_0_28, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|v1_xboole_0(X3)|m1_subset_1(k1_tmap_1(X4,X1,X2,X3,X5,X6),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4,X2,X3),X1)))|~v1_funct_2(X6,X3,X1)|~v1_funct_2(X5,X2,X1)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~m1_subset_1(X3,k1_zfmisc_1(X4))|~m1_subset_1(X2,k1_zfmisc_1(X4))), inference(csr,[status(thm)],[c_0_23, c_0_22])).
% 0.39/0.56  cnf(c_0_29, plain, (v1_funct_1(k1_tmap_1(X1,X2,X3,X4,X5,X6))|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_24, c_0_22])).
% 0.39/0.56  cnf(c_0_30, plain, (v1_funct_2(k1_tmap_1(X1,X2,X3,X4,X5,X6),k4_subset_1(X1,X3,X4),X2)|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|~v1_funct_2(X6,X4,X2)|~v1_funct_2(X5,X3,X2)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_25, c_0_22])).
% 0.39/0.56  cnf(c_0_31, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X3)|v1_xboole_0(X2)|v1_xboole_0(X4)|v1_xboole_0(X1)|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_1(X5)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|~v1_funct_1(X7)|~v1_funct_2(X7,X3,X4)|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X6)|~v1_funct_2(X6,X2,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.39/0.56  fof(c_0_32, plain, ![X36, X37]:((~v1_partfun1(X37,X36)|k1_relat_1(X37)=X36|(~v1_relat_1(X37)|~v4_relat_1(X37,X36)))&(k1_relat_1(X37)!=X36|v1_partfun1(X37,X36)|(~v1_relat_1(X37)|~v4_relat_1(X37,X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.39/0.56  fof(c_0_33, plain, ![X42]:((((v1_relat_1(esk1_1(X42))&v4_relat_1(esk1_1(X42),X42))&v1_funct_1(esk1_1(X42)))&v1_partfun1(esk1_1(X42),X42))&v1_yellow_1(esk1_1(X42))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_yellow_1])])).
% 0.39/0.56  fof(c_0_34, plain, ![X44]:(~v1_relat_1(X44)|~v4_relat_1(X44,k1_xboole_0)|~v1_funct_1(X44)|~v1_partfun1(X44,k1_xboole_0)|X44=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t134_pboole])])).
% 0.39/0.56  cnf(c_0_35, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk5_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_36, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X3)=X6|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X5,X2,X4)|~v1_funct_2(X6,X3,X4)|~v1_funct_1(X5)|~v1_funct_1(X6)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.39/0.56  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_45, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_47, negated_conjecture, (~v1_xboole_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_48, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,X5,X2)=X6|v1_xboole_0(X2)|v1_xboole_0(X3)|v1_xboole_0(X4)|k2_partfun1(X2,X4,X6,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X7,k9_subset_1(X1,X2,X3))|X5!=k1_tmap_1(X1,X4,X2,X3,X6,X7)|~v1_funct_2(X5,k4_subset_1(X1,X2,X3),X4)|~v1_funct_2(X7,X3,X4)|~v1_funct_2(X6,X2,X4)|~v1_funct_1(X7)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1,X2,X3),X4)))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[c_0_31, c_0_22])).
% 0.39/0.56  fof(c_0_49, plain, ![X38, X39, X40, X41]:(~v1_funct_1(X40)|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k2_partfun1(X38,X39,X40,X41)=k7_relat_1(X40,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.39/0.56  fof(c_0_50, plain, ![X33, X34, X35]:((v1_funct_1(X35)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_xboole_0(X34))&(v1_partfun1(X35,X33)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|v1_xboole_0(X34))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.39/0.56  fof(c_0_51, plain, ![X30, X31, X32]:((v4_relat_1(X32,X30)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))&(v5_relat_1(X32,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.39/0.56  fof(c_0_52, plain, ![X27, X28, X29]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_relat_1(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.39/0.56  fof(c_0_53, plain, ![X23, X24]:(~v1_relat_1(X24)|k1_relat_1(k7_relat_1(X24,X23))=k3_xboole_0(k1_relat_1(X24),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t90_relat_1])])).
% 0.39/0.56  cnf(c_0_54, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.39/0.56  cnf(c_0_55, plain, (v1_partfun1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  cnf(c_0_56, plain, (v4_relat_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  cnf(c_0_57, plain, (v1_relat_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  fof(c_0_58, plain, ![X19, X20]:(~v1_relat_1(X19)|(~r1_xboole_0(X20,k1_relat_1(X19))|k7_relat_1(X19,X20)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t187_relat_1])])])).
% 0.39/0.56  cnf(c_0_59, plain, (X1=k1_xboole_0|~v1_relat_1(X1)|~v4_relat_1(X1,k1_xboole_0)|~v1_funct_1(X1)|~v1_partfun1(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.39/0.56  cnf(c_0_60, plain, (v1_funct_1(esk1_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.39/0.56  cnf(c_0_61, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|k2_partfun1(k4_subset_1(esk2_0,esk4_0,esk5_0),esk3_0,k1_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0,esk6_0,esk7_0),esk4_0)!=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44])]), c_0_45]), c_0_46]), c_0_47])).
% 0.39/0.56  cnf(c_0_62, plain, (k2_partfun1(k4_subset_1(X1,X2,X3),X4,k1_tmap_1(X1,X4,X2,X3,X5,X6),X2)=X5|v1_xboole_0(X4)|v1_xboole_0(X3)|v1_xboole_0(X2)|k2_partfun1(X2,X4,X5,k9_subset_1(X1,X2,X3))!=k2_partfun1(X3,X4,X6,k9_subset_1(X1,X2,X3))|~v1_funct_2(X6,X3,X4)|~v1_funct_2(X5,X2,X4)|~v1_funct_1(X6)|~v1_funct_1(X5)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_28]), c_0_29]), c_0_30])).
% 0.39/0.56  cnf(c_0_63, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.39/0.56  cnf(c_0_64, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.39/0.56  cnf(c_0_65, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.39/0.56  cnf(c_0_66, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.39/0.56  cnf(c_0_67, plain, (k1_relat_1(k7_relat_1(X1,X2))=k3_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.39/0.56  cnf(c_0_68, plain, (k1_relat_1(esk1_1(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_57])])).
% 0.39/0.56  cnf(c_0_69, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.39/0.56  cnf(c_0_70, plain, (esk1_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_55]), c_0_60]), c_0_56]), c_0_57])])).
% 0.39/0.56  fof(c_0_71, plain, ![X25, X26]:((~r1_subset_1(X25,X26)|r1_xboole_0(X25,X26)|(v1_xboole_0(X25)|v1_xboole_0(X26)))&(~r1_xboole_0(X25,X26)|r1_subset_1(X25,X26)|(v1_xboole_0(X25)|v1_xboole_0(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).
% 0.39/0.56  cnf(c_0_72, negated_conjecture, (k2_partfun1(esk5_0,esk3_0,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_38]), c_0_37]), c_0_40]), c_0_39]), c_0_42]), c_0_41]), c_0_43]), c_0_44])]), c_0_45]), c_0_46]), c_0_47])).
% 0.39/0.56  cnf(c_0_73, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_63, c_0_63])).
% 0.39/0.56  fof(c_0_74, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(X10))|k9_subset_1(X10,X11,X12)=k3_xboole_0(X11,X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 0.39/0.56  fof(c_0_75, plain, ![X21, X22]:(~v1_relat_1(X22)|k7_relat_1(X22,X21)=k7_relat_1(X22,k3_xboole_0(k1_relat_1(X22),X21))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t192_relat_1])])).
% 0.39/0.56  cnf(c_0_76, negated_conjecture, (v1_partfun1(esk7_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_42]), c_0_38]), c_0_40])]), c_0_45])).
% 0.39/0.56  cnf(c_0_77, negated_conjecture, (v4_relat_1(esk7_0,esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_42])).
% 0.39/0.56  cnf(c_0_78, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_42])).
% 0.39/0.56  cnf(c_0_79, plain, (k1_relat_1(k7_relat_1(esk1_1(X1),X2))=k3_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_57])])).
% 0.39/0.56  cnf(c_0_80, plain, (k7_relat_1(esk1_1(X1),X2)=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_57])])).
% 0.39/0.56  cnf(c_0_81, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_70])).
% 0.39/0.56  cnf(c_0_82, plain, (r1_xboole_0(X1,X2)|v1_xboole_0(X1)|v1_xboole_0(X2)|~r1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.39/0.56  cnf(c_0_83, negated_conjecture, (r1_subset_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.39/0.56  cnf(c_0_84, negated_conjecture, (k2_partfun1(X1,X2,esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_40]), c_0_42])])).
% 0.39/0.56  cnf(c_0_85, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.39/0.56  cnf(c_0_86, plain, (k7_relat_1(X1,X2)=k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.39/0.56  cnf(c_0_87, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_76]), c_0_77]), c_0_78])])).
% 0.39/0.56  cnf(c_0_88, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X2,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.39/0.56  cnf(c_0_89, negated_conjecture, (r1_xboole_0(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_47]), c_0_46])).
% 0.39/0.56  cnf(c_0_90, negated_conjecture, (v1_partfun1(esk6_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_41]), c_0_37]), c_0_39])]), c_0_45])).
% 0.39/0.56  cnf(c_0_91, negated_conjecture, (v4_relat_1(esk6_0,esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_41])).
% 0.39/0.56  cnf(c_0_92, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_66, c_0_41])).
% 0.39/0.56  cnf(c_0_93, negated_conjecture, (k7_relat_1(esk7_0,k9_subset_1(esk2_0,esk4_0,esk5_0))!=k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(esk2_0,esk4_0,esk5_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_63]), c_0_40])])).
% 0.39/0.56  cnf(c_0_94, plain, (k9_subset_1(X1,X2,X3)=k9_subset_1(X4,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(X1))|~m1_subset_1(X3,k1_zfmisc_1(X4))), inference(spm,[status(thm)],[c_0_85, c_0_85])).
% 0.39/0.56  fof(c_0_95, plain, ![X8, X9]:((~r1_xboole_0(X8,X9)|k3_xboole_0(X8,X9)=k1_xboole_0)&(k3_xboole_0(X8,X9)!=k1_xboole_0|r1_xboole_0(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).
% 0.39/0.56  cnf(c_0_96, negated_conjecture, (k7_relat_1(esk7_0,k3_xboole_0(esk5_0,X1))=k7_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_78])])).
% 0.39/0.56  cnf(c_0_97, negated_conjecture, (k3_xboole_0(esk5_0,esk4_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_88, c_0_89])).
% 0.39/0.56  cnf(c_0_98, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_90]), c_0_91]), c_0_92])])).
% 0.39/0.56  cnf(c_0_99, negated_conjecture, (k7_relat_1(esk7_0,k9_subset_1(X1,esk4_0,esk5_0))!=k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(X1,esk4_0,esk5_0))|~m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_43])])).
% 0.39/0.56  cnf(c_0_100, plain, (k3_xboole_0(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.39/0.56  cnf(c_0_101, negated_conjecture, (k7_relat_1(esk7_0,esk4_0)=k7_relat_1(esk7_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.39/0.56  cnf(c_0_102, negated_conjecture, (k7_relat_1(esk7_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_87]), c_0_78])])).
% 0.39/0.56  cnf(c_0_103, plain, (k7_relat_1(X1,k1_relat_1(k7_relat_1(X1,X2)))=k7_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_86, c_0_67])).
% 0.39/0.56  cnf(c_0_104, negated_conjecture, (k7_relat_1(esk6_0,X1)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_98]), c_0_92])])).
% 0.39/0.56  cnf(c_0_105, negated_conjecture, (k7_relat_1(esk7_0,k9_subset_1(X1,esk4_0,esk5_0))!=k2_partfun1(esk4_0,esk3_0,esk6_0,k9_subset_1(X1,esk4_0,esk5_0))|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_99, c_0_42])).
% 0.39/0.56  cnf(c_0_106, negated_conjecture, (k3_xboole_0(esk4_0,esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_100, c_0_89])).
% 0.39/0.56  cnf(c_0_107, negated_conjecture, (k7_relat_1(esk7_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_89])])).
% 0.39/0.56  cnf(c_0_108, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0|~r1_xboole_0(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_81]), c_0_92])])).
% 0.39/0.56  cnf(c_0_109, plain, (r1_xboole_0(X1,X2)|k3_xboole_0(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.39/0.56  cnf(c_0_110, negated_conjecture, (k2_partfun1(esk4_0,esk3_0,esk6_0,k1_xboole_0)!=k1_xboole_0|~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_85]), c_0_106]), c_0_107]), c_0_106])).
% 0.39/0.56  cnf(c_0_111, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0|k3_xboole_0(X1,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_108, c_0_109])).
% 0.39/0.56  cnf(c_0_112, negated_conjecture, (k2_partfun1(X1,X2,esk6_0,k1_xboole_0)!=k1_xboole_0|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_73]), c_0_39]), c_0_41])])).
% 0.39/0.56  cnf(c_0_113, negated_conjecture, (k7_relat_1(esk6_0,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_111, c_0_97])).
% 0.39/0.56  cnf(c_0_114, negated_conjecture, (~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(esk5_0,k1_zfmisc_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112, c_0_63]), c_0_113]), c_0_39])])).
% 0.39/0.56  cnf(c_0_115, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_114, c_0_41])).
% 0.39/0.56  cnf(c_0_116, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_43, c_0_115]), ['proof']).
% 0.39/0.56  # SZS output end CNFRefutation
% 0.39/0.56  # Proof object total steps             : 117
% 0.39/0.56  # Proof object clause steps            : 82
% 0.39/0.56  # Proof object formula steps           : 35
% 0.39/0.56  # Proof object conjectures             : 46
% 0.39/0.56  # Proof object clause conjectures      : 43
% 0.39/0.56  # Proof object formula conjectures     : 3
% 0.39/0.56  # Proof object initial clauses used    : 36
% 0.39/0.56  # Proof object initial formulas used   : 17
% 0.39/0.56  # Proof object generating inferences   : 40
% 0.39/0.56  # Proof object simplifying inferences  : 91
% 0.39/0.56  # Training examples: 0 positive, 0 negative
% 0.39/0.56  # Parsed axioms                        : 19
% 0.39/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.39/0.56  # Initial clauses                      : 45
% 0.39/0.56  # Removed in clause preprocessing      : 1
% 0.39/0.56  # Initial clauses in saturation        : 44
% 0.39/0.56  # Processed clauses                    : 499
% 0.39/0.56  # ...of these trivial                  : 21
% 0.39/0.56  # ...subsumed                          : 205
% 0.39/0.56  # ...remaining for further processing  : 273
% 0.39/0.56  # Other redundant clauses eliminated   : 24
% 0.39/0.56  # Clauses deleted for lack of memory   : 0
% 0.39/0.56  # Backward-subsumed                    : 17
% 0.39/0.56  # Backward-rewritten                   : 18
% 0.39/0.56  # Generated clauses                    : 3331
% 0.39/0.56  # ...of the previous two non-trivial   : 3168
% 0.39/0.56  # Contextual simplify-reflections      : 27
% 0.39/0.56  # Paramodulations                      : 3281
% 0.39/0.56  # Factorizations                       : 0
% 0.39/0.56  # Equation resolutions                 : 49
% 0.39/0.56  # Propositional unsat checks           : 0
% 0.39/0.56  #    Propositional check models        : 0
% 0.39/0.56  #    Propositional check unsatisfiable : 0
% 0.39/0.56  #    Propositional clauses             : 0
% 0.39/0.56  #    Propositional clauses after purity: 0
% 0.39/0.56  #    Propositional unsat core size     : 0
% 0.39/0.56  #    Propositional preprocessing time  : 0.000
% 0.39/0.56  #    Propositional encoding time       : 0.000
% 0.39/0.56  #    Propositional solver time         : 0.000
% 0.39/0.56  #    Success case prop preproc time    : 0.000
% 0.39/0.56  #    Success case prop encoding time   : 0.000
% 0.39/0.56  #    Success case prop solver time     : 0.000
% 0.39/0.56  # Current number of processed clauses  : 237
% 0.39/0.56  #    Positive orientable unit clauses  : 67
% 0.39/0.56  #    Positive unorientable unit clauses: 4
% 0.39/0.56  #    Negative unit clauses             : 6
% 0.39/0.56  #    Non-unit-clauses                  : 160
% 0.39/0.56  # Current number of unprocessed clauses: 2645
% 0.39/0.56  # ...number of literals in the above   : 25629
% 0.39/0.56  # Current number of archived formulas  : 0
% 0.39/0.56  # Current number of archived clauses   : 36
% 0.39/0.56  # Clause-clause subsumption calls (NU) : 42266
% 0.39/0.56  # Rec. Clause-clause subsumption calls : 4676
% 0.39/0.56  # Non-unit clause-clause subsumptions  : 226
% 0.39/0.56  # Unit Clause-clause subsumption calls : 3286
% 0.39/0.56  # Rewrite failures with RHS unbound    : 32
% 0.39/0.56  # BW rewrite match attempts            : 511
% 0.39/0.56  # BW rewrite match successes           : 14
% 0.39/0.56  # Condensation attempts                : 0
% 0.39/0.56  # Condensation successes               : 0
% 0.39/0.56  # Termbank termtop insertions          : 145172
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.202 s
% 0.39/0.56  # System time              : 0.016 s
% 0.39/0.56  # Total time               : 0.218 s
% 0.39/0.56  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
