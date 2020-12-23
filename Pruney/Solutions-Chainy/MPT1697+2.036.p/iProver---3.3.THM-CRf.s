%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:29 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  182 (1242 expanded)
%              Number of clauses        :  106 ( 314 expanded)
%              Number of leaves         :   20 ( 475 expanded)
%              Depth                    :   19
%              Number of atoms          : 1058 (15327 expanded)
%              Number of equality atoms :  342 (3573 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK8),X3) != sK8
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK8),X2) != X4
          | k2_partfun1(X3,X1,sK8,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK8,X3,X1)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
              & v1_funct_2(X5,X3,X1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          & v1_funct_2(X4,X2,X1)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK7,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK7,X5),X2) != sK7
              | k2_partfun1(X2,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK7,X2,X1)
        & v1_funct_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                    | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                  & v1_funct_2(X5,X3,X1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(X4,X2,X1)
              & v1_funct_1(X4) )
          & r1_subset_1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X3) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK6),X1,k1_tmap_1(X0,X1,X2,sK6,X4,X5),sK6) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK6),X1,k1_tmap_1(X0,X1,X2,sK6,X4,X5),X2) != X4
                  | k2_partfun1(sK6,X1,X5,k9_subset_1(X0,X2,sK6)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK6)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,X1)))
                & v1_funct_2(X5,sK6,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK6)
        & m1_subset_1(sK6,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      & v1_funct_2(X5,X3,X1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                  & v1_funct_2(X4,X2,X1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(X0))
          & ~ v1_xboole_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(X0,sK5,X3),X1,k1_tmap_1(X0,X1,sK5,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK5,X3),X1,k1_tmap_1(X0,X1,sK5,X3,X4,X5),sK5) != X4
                      | k2_partfun1(sK5,X1,X4,k9_subset_1(X0,sK5,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK5,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,X1)))
                & v1_funct_2(X4,sK5,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK5,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK5,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK4,k1_tmap_1(X0,sK4,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK4,k1_tmap_1(X0,sK4,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK4,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                        & v1_funct_2(X5,X3,sK4)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
                    & v1_funct_2(X4,X2,sK4)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK3))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK3))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
      | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
      | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_2(sK8,sK6,sK4)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    & v1_funct_2(sK7,sK5,sK4)
    & v1_funct_1(sK7)
    & r1_subset_1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & ~ v1_xboole_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(sK3))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f34,f51,f50,f49,f48,f47,f46])).

fof(f87,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    r1_subset_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f77,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f39])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f62,f61])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f41])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f83,plain,(
    v1_funct_2(sK7,sK5,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_2(sK8,sK6,sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f88,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
    | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_654,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1283,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_654])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_661,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1277,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_2129,plain,
    ( v1_relat_1(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1277])).

cnf(c_12,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_394,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK6 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_395,plain,
    ( r1_xboole_0(sK5,sK6)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_397,plain,
    ( r1_xboole_0(sK5,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_32,c_30])).

cnf(c_640,plain,
    ( r1_xboole_0(sK5,sK6) ),
    inference(subtyping,[status(esa)],[c_397])).

cnf(c_1297,plain,
    ( r1_xboole_0(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_667,plain,
    ( r1_xboole_0(X0_55,X1_55)
    | r2_hidden(sK1(X0_55,X1_55),X0_55) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1271,plain,
    ( r1_xboole_0(X0_55,X1_55) = iProver_top
    | r2_hidden(sK1(X0_55,X1_55),X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_648,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1289,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_664,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | k4_xboole_0(X2_55,k4_xboole_0(X2_55,X0_55)) = k9_subset_1(X1_55,X2_55,X0_55) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1274,plain,
    ( k4_xboole_0(X0_55,k4_xboole_0(X0_55,X1_55)) = k9_subset_1(X2_55,X0_55,X1_55)
    | m1_subset_1(X1_55,k1_zfmisc_1(X2_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_2215,plain,
    ( k4_xboole_0(X0_55,k4_xboole_0(X0_55,sK6)) = k9_subset_1(sK3,X0_55,sK6) ),
    inference(superposition,[status(thm)],[c_1289,c_1274])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_666,plain,
    ( ~ r1_xboole_0(X0_55,X1_55)
    | ~ r2_hidden(X0_57,k4_xboole_0(X0_55,k4_xboole_0(X0_55,X1_55))) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1272,plain,
    ( r1_xboole_0(X0_55,X1_55) != iProver_top
    | r2_hidden(X0_57,k4_xboole_0(X0_55,k4_xboole_0(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_2719,plain,
    ( r1_xboole_0(X0_55,sK6) != iProver_top
    | r2_hidden(X0_57,k9_subset_1(sK3,X0_55,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2215,c_1272])).

cnf(c_2930,plain,
    ( r1_xboole_0(X0_55,sK6) != iProver_top
    | r1_xboole_0(k9_subset_1(sK3,X0_55,sK6),X1_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_1271,c_2719])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_662,plain,
    ( ~ r1_xboole_0(X0_55,k1_relat_1(X1_55))
    | ~ v1_relat_1(X1_55)
    | k7_relat_1(X1_55,X0_55) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1276,plain,
    ( k7_relat_1(X0_55,X1_55) = k1_xboole_0
    | r1_xboole_0(X1_55,k1_relat_1(X0_55)) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_5053,plain,
    ( k7_relat_1(X0_55,k9_subset_1(sK3,X1_55,sK6)) = k1_xboole_0
    | r1_xboole_0(X1_55,sK6) != iProver_top
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_1276])).

cnf(c_11371,plain,
    ( k7_relat_1(X0_55,k9_subset_1(sK3,sK5,sK6)) = k1_xboole_0
    | v1_relat_1(X0_55) != iProver_top ),
    inference(superposition,[status(thm)],[c_1297,c_5053])).

cnf(c_11855,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2129,c_11371])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_660,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1278,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_3254,plain,
    ( k2_partfun1(sK6,sK4,sK8,X0_55) = k7_relat_1(sK8,X0_55)
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1278])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1704,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK8)
    | k2_partfun1(X0_55,X1_55,sK8,X2_55) = k7_relat_1(sK8,X2_55) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1863,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | k2_partfun1(sK6,sK4,sK8,X0_55) = k7_relat_1(sK8,X0_55) ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_3526,plain,
    ( k2_partfun1(sK6,sK4,sK8,X0_55) = k7_relat_1(sK8,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3254,c_24,c_22,c_1863])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_651,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1286,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_3255,plain,
    ( k2_partfun1(sK5,sK4,sK7,X0_55) = k7_relat_1(sK7,X0_55)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1278])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1709,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(X0_55,X1_55,sK7,X2_55) = k7_relat_1(sK7,X2_55) ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1868,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | k2_partfun1(sK5,sK4,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
    inference(instantiation,[status(thm)],[c_1709])).

cnf(c_3616,plain,
    ( k2_partfun1(sK5,sK4,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3255,c_27,c_25,c_1868])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_186,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_20,c_19,c_18])).

cnf(c_187,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_642,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_1295,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_663,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | ~ v1_xboole_0(X1_55)
    | v1_xboole_0(X0_55) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1275,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
    | v1_xboole_0(X1_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_1482,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
    | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X0_55) = X2_55
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1295,c_1275])).

cnf(c_6388,plain,
    ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),sK5) = sK7
    | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
    | v1_funct_2(sK7,sK5,sK4) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3616,c_1482])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_43,plain,
    ( v1_funct_2(sK7,sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8499,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),sK5) = sK7
    | k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6388,c_36,c_37,c_42,c_43,c_44])).

cnf(c_8500,plain,
    ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),sK5) = sK7
    | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_8499])).

cnf(c_8513,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
    | v1_funct_2(sK8,sK6,sK4) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_8500])).

cnf(c_39,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_46,plain,
    ( v1_funct_2(sK8,sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9098,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
    | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8513,c_39,c_45,c_46,c_47])).

cnf(c_11926,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11855,c_9098])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_193,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_20,c_19,c_18])).

cnf(c_194,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X5)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(renaming,[status(thm)],[c_193])).

cnf(c_641,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_1296,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_1510,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
    | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X4_55) = X5_55
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1296,c_1275])).

cnf(c_8676,plain,
    ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
    | v1_funct_2(sK7,sK5,sK4) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3616,c_1510])).

cnf(c_9968,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),X0_55) = X1_55
    | k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8676,c_36,c_37,c_42,c_43,c_44])).

cnf(c_9969,plain,
    ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
    | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_9968])).

cnf(c_9982,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK6) = sK8
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
    | v1_funct_2(sK8,sK6,sK4) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_9969])).

cnf(c_10153,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK6) = sK8
    | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
    | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9982,c_39,c_45,c_46,c_47])).

cnf(c_11925,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) = sK8
    | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11855,c_10153])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
    | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_655,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
    | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_3530,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
    | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_3526,c_655])).

cnf(c_3620,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
    | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
    | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(demodulation,[status(thm)],[c_3616,c_3530])).

cnf(c_11924,plain,
    ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
    | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
    | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11855,c_3620])).

cnf(c_2130,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_1277])).

cnf(c_11856,plain,
    ( k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2130,c_11371])).

cnf(c_40,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11926,c_11925,c_11924,c_11856,c_40,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 5.97/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/1.49  
% 5.97/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 5.97/1.49  
% 5.97/1.49  ------  iProver source info
% 5.97/1.49  
% 5.97/1.49  git: date: 2020-06-30 10:37:57 +0100
% 5.97/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 5.97/1.49  git: non_committed_changes: false
% 5.97/1.49  git: last_make_outside_of_git: false
% 5.97/1.49  
% 5.97/1.49  ------ 
% 5.97/1.49  
% 5.97/1.49  ------ Input Options
% 5.97/1.49  
% 5.97/1.49  --out_options                           all
% 5.97/1.49  --tptp_safe_out                         true
% 5.97/1.49  --problem_path                          ""
% 5.97/1.49  --include_path                          ""
% 5.97/1.49  --clausifier                            res/vclausify_rel
% 5.97/1.49  --clausifier_options                    --mode clausify
% 5.97/1.49  --stdin                                 false
% 5.97/1.49  --stats_out                             all
% 5.97/1.49  
% 5.97/1.49  ------ General Options
% 5.97/1.49  
% 5.97/1.49  --fof                                   false
% 5.97/1.49  --time_out_real                         305.
% 5.97/1.49  --time_out_virtual                      -1.
% 5.97/1.49  --symbol_type_check                     false
% 5.97/1.49  --clausify_out                          false
% 5.97/1.49  --sig_cnt_out                           false
% 5.97/1.49  --trig_cnt_out                          false
% 5.97/1.49  --trig_cnt_out_tolerance                1.
% 5.97/1.49  --trig_cnt_out_sk_spl                   false
% 5.97/1.49  --abstr_cl_out                          false
% 5.97/1.49  
% 5.97/1.49  ------ Global Options
% 5.97/1.49  
% 5.97/1.49  --schedule                              default
% 5.97/1.49  --add_important_lit                     false
% 5.97/1.49  --prop_solver_per_cl                    1000
% 5.97/1.49  --min_unsat_core                        false
% 5.97/1.49  --soft_assumptions                      false
% 5.97/1.49  --soft_lemma_size                       3
% 5.97/1.49  --prop_impl_unit_size                   0
% 5.97/1.49  --prop_impl_unit                        []
% 5.97/1.49  --share_sel_clauses                     true
% 5.97/1.49  --reset_solvers                         false
% 5.97/1.49  --bc_imp_inh                            [conj_cone]
% 5.97/1.49  --conj_cone_tolerance                   3.
% 5.97/1.49  --extra_neg_conj                        none
% 5.97/1.49  --large_theory_mode                     true
% 5.97/1.49  --prolific_symb_bound                   200
% 5.97/1.49  --lt_threshold                          2000
% 5.97/1.49  --clause_weak_htbl                      true
% 5.97/1.49  --gc_record_bc_elim                     false
% 5.97/1.49  
% 5.97/1.49  ------ Preprocessing Options
% 5.97/1.49  
% 5.97/1.49  --preprocessing_flag                    true
% 5.97/1.49  --time_out_prep_mult                    0.1
% 5.97/1.49  --splitting_mode                        input
% 5.97/1.49  --splitting_grd                         true
% 5.97/1.49  --splitting_cvd                         false
% 5.97/1.49  --splitting_cvd_svl                     false
% 5.97/1.49  --splitting_nvd                         32
% 5.97/1.49  --sub_typing                            true
% 5.97/1.49  --prep_gs_sim                           true
% 5.97/1.49  --prep_unflatten                        true
% 5.97/1.49  --prep_res_sim                          true
% 5.97/1.49  --prep_upred                            true
% 5.97/1.49  --prep_sem_filter                       exhaustive
% 5.97/1.49  --prep_sem_filter_out                   false
% 5.97/1.49  --pred_elim                             true
% 5.97/1.49  --res_sim_input                         true
% 5.97/1.49  --eq_ax_congr_red                       true
% 5.97/1.49  --pure_diseq_elim                       true
% 5.97/1.49  --brand_transform                       false
% 5.97/1.49  --non_eq_to_eq                          false
% 5.97/1.49  --prep_def_merge                        true
% 5.97/1.49  --prep_def_merge_prop_impl              false
% 5.97/1.49  --prep_def_merge_mbd                    true
% 5.97/1.49  --prep_def_merge_tr_red                 false
% 5.97/1.49  --prep_def_merge_tr_cl                  false
% 5.97/1.49  --smt_preprocessing                     true
% 5.97/1.49  --smt_ac_axioms                         fast
% 5.97/1.49  --preprocessed_out                      false
% 5.97/1.49  --preprocessed_stats                    false
% 5.97/1.49  
% 5.97/1.49  ------ Abstraction refinement Options
% 5.97/1.49  
% 5.97/1.49  --abstr_ref                             []
% 5.97/1.49  --abstr_ref_prep                        false
% 5.97/1.49  --abstr_ref_until_sat                   false
% 5.97/1.49  --abstr_ref_sig_restrict                funpre
% 5.97/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 5.97/1.49  --abstr_ref_under                       []
% 5.97/1.49  
% 5.97/1.49  ------ SAT Options
% 5.97/1.49  
% 5.97/1.49  --sat_mode                              false
% 5.97/1.49  --sat_fm_restart_options                ""
% 5.97/1.49  --sat_gr_def                            false
% 5.97/1.49  --sat_epr_types                         true
% 5.97/1.49  --sat_non_cyclic_types                  false
% 5.97/1.49  --sat_finite_models                     false
% 5.97/1.49  --sat_fm_lemmas                         false
% 5.97/1.49  --sat_fm_prep                           false
% 5.97/1.49  --sat_fm_uc_incr                        true
% 5.97/1.49  --sat_out_model                         small
% 5.97/1.49  --sat_out_clauses                       false
% 5.97/1.49  
% 5.97/1.49  ------ QBF Options
% 5.97/1.49  
% 5.97/1.49  --qbf_mode                              false
% 5.97/1.49  --qbf_elim_univ                         false
% 5.97/1.49  --qbf_dom_inst                          none
% 5.97/1.49  --qbf_dom_pre_inst                      false
% 5.97/1.49  --qbf_sk_in                             false
% 5.97/1.49  --qbf_pred_elim                         true
% 5.97/1.49  --qbf_split                             512
% 5.97/1.49  
% 5.97/1.49  ------ BMC1 Options
% 5.97/1.49  
% 5.97/1.49  --bmc1_incremental                      false
% 5.97/1.49  --bmc1_axioms                           reachable_all
% 5.97/1.49  --bmc1_min_bound                        0
% 5.97/1.49  --bmc1_max_bound                        -1
% 5.97/1.49  --bmc1_max_bound_default                -1
% 5.97/1.49  --bmc1_symbol_reachability              true
% 5.97/1.49  --bmc1_property_lemmas                  false
% 5.97/1.49  --bmc1_k_induction                      false
% 5.97/1.49  --bmc1_non_equiv_states                 false
% 5.97/1.49  --bmc1_deadlock                         false
% 5.97/1.49  --bmc1_ucm                              false
% 5.97/1.49  --bmc1_add_unsat_core                   none
% 5.97/1.49  --bmc1_unsat_core_children              false
% 5.97/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 5.97/1.49  --bmc1_out_stat                         full
% 5.97/1.49  --bmc1_ground_init                      false
% 5.97/1.49  --bmc1_pre_inst_next_state              false
% 5.97/1.49  --bmc1_pre_inst_state                   false
% 5.97/1.49  --bmc1_pre_inst_reach_state             false
% 5.97/1.49  --bmc1_out_unsat_core                   false
% 5.97/1.49  --bmc1_aig_witness_out                  false
% 5.97/1.49  --bmc1_verbose                          false
% 5.97/1.49  --bmc1_dump_clauses_tptp                false
% 5.97/1.49  --bmc1_dump_unsat_core_tptp             false
% 5.97/1.49  --bmc1_dump_file                        -
% 5.97/1.49  --bmc1_ucm_expand_uc_limit              128
% 5.97/1.49  --bmc1_ucm_n_expand_iterations          6
% 5.97/1.49  --bmc1_ucm_extend_mode                  1
% 5.97/1.49  --bmc1_ucm_init_mode                    2
% 5.97/1.49  --bmc1_ucm_cone_mode                    none
% 5.97/1.49  --bmc1_ucm_reduced_relation_type        0
% 5.97/1.49  --bmc1_ucm_relax_model                  4
% 5.97/1.49  --bmc1_ucm_full_tr_after_sat            true
% 5.97/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 5.97/1.49  --bmc1_ucm_layered_model                none
% 5.97/1.49  --bmc1_ucm_max_lemma_size               10
% 5.97/1.49  
% 5.97/1.49  ------ AIG Options
% 5.97/1.49  
% 5.97/1.49  --aig_mode                              false
% 5.97/1.49  
% 5.97/1.49  ------ Instantiation Options
% 5.97/1.49  
% 5.97/1.49  --instantiation_flag                    true
% 5.97/1.49  --inst_sos_flag                         false
% 5.97/1.49  --inst_sos_phase                        true
% 5.97/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 5.97/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 5.97/1.49  --inst_lit_sel_side                     num_symb
% 5.97/1.49  --inst_solver_per_active                1400
% 5.97/1.49  --inst_solver_calls_frac                1.
% 5.97/1.49  --inst_passive_queue_type               priority_queues
% 5.97/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 5.97/1.49  --inst_passive_queues_freq              [25;2]
% 5.97/1.49  --inst_dismatching                      true
% 5.97/1.49  --inst_eager_unprocessed_to_passive     true
% 5.97/1.49  --inst_prop_sim_given                   true
% 5.97/1.49  --inst_prop_sim_new                     false
% 5.97/1.49  --inst_subs_new                         false
% 5.97/1.49  --inst_eq_res_simp                      false
% 5.97/1.49  --inst_subs_given                       false
% 5.97/1.49  --inst_orphan_elimination               true
% 5.97/1.49  --inst_learning_loop_flag               true
% 5.97/1.49  --inst_learning_start                   3000
% 5.97/1.49  --inst_learning_factor                  2
% 5.97/1.49  --inst_start_prop_sim_after_learn       3
% 5.97/1.49  --inst_sel_renew                        solver
% 5.97/1.49  --inst_lit_activity_flag                true
% 5.97/1.49  --inst_restr_to_given                   false
% 5.97/1.49  --inst_activity_threshold               500
% 5.97/1.49  --inst_out_proof                        true
% 5.97/1.49  
% 5.97/1.49  ------ Resolution Options
% 5.97/1.49  
% 5.97/1.49  --resolution_flag                       true
% 5.97/1.49  --res_lit_sel                           adaptive
% 5.97/1.49  --res_lit_sel_side                      none
% 5.97/1.49  --res_ordering                          kbo
% 5.97/1.49  --res_to_prop_solver                    active
% 5.97/1.49  --res_prop_simpl_new                    false
% 5.97/1.49  --res_prop_simpl_given                  true
% 5.97/1.49  --res_passive_queue_type                priority_queues
% 5.97/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 5.97/1.49  --res_passive_queues_freq               [15;5]
% 5.97/1.49  --res_forward_subs                      full
% 5.97/1.49  --res_backward_subs                     full
% 5.97/1.49  --res_forward_subs_resolution           true
% 5.97/1.49  --res_backward_subs_resolution          true
% 5.97/1.49  --res_orphan_elimination                true
% 5.97/1.49  --res_time_limit                        2.
% 5.97/1.49  --res_out_proof                         true
% 5.97/1.49  
% 5.97/1.49  ------ Superposition Options
% 5.97/1.49  
% 5.97/1.49  --superposition_flag                    true
% 5.97/1.49  --sup_passive_queue_type                priority_queues
% 5.97/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 5.97/1.49  --sup_passive_queues_freq               [8;1;4]
% 5.97/1.49  --demod_completeness_check              fast
% 5.97/1.49  --demod_use_ground                      true
% 5.97/1.49  --sup_to_prop_solver                    passive
% 5.97/1.49  --sup_prop_simpl_new                    true
% 5.97/1.49  --sup_prop_simpl_given                  true
% 5.97/1.49  --sup_fun_splitting                     false
% 5.97/1.49  --sup_smt_interval                      50000
% 5.97/1.49  
% 5.97/1.49  ------ Superposition Simplification Setup
% 5.97/1.49  
% 5.97/1.49  --sup_indices_passive                   []
% 5.97/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.97/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.97/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.97/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 5.97/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.97/1.49  --sup_full_bw                           [BwDemod]
% 5.97/1.49  --sup_immed_triv                        [TrivRules]
% 5.97/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 5.97/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.97/1.49  --sup_immed_bw_main                     []
% 5.97/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.97/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 5.97/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.97/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.97/1.49  
% 5.97/1.49  ------ Combination Options
% 5.97/1.49  
% 5.97/1.49  --comb_res_mult                         3
% 5.97/1.49  --comb_sup_mult                         2
% 5.97/1.49  --comb_inst_mult                        10
% 5.97/1.49  
% 5.97/1.49  ------ Debug Options
% 5.97/1.49  
% 5.97/1.49  --dbg_backtrace                         false
% 5.97/1.49  --dbg_dump_prop_clauses                 false
% 5.97/1.49  --dbg_dump_prop_clauses_file            -
% 5.97/1.49  --dbg_out_stat                          false
% 5.97/1.49  ------ Parsing...
% 5.97/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 5.97/1.49  
% 5.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 5.97/1.49  
% 5.97/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 5.97/1.49  
% 5.97/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 5.97/1.49  ------ Proving...
% 5.97/1.49  ------ Problem Properties 
% 5.97/1.49  
% 5.97/1.49  
% 5.97/1.49  clauses                                 33
% 5.97/1.49  conjectures                             13
% 5.97/1.49  EPR                                     12
% 5.97/1.49  Horn                                    23
% 5.97/1.49  unary                                   13
% 5.97/1.49  binary                                  9
% 5.97/1.49  lits                                    130
% 5.97/1.49  lits eq                                 12
% 5.97/1.49  fd_pure                                 0
% 5.97/1.49  fd_pseudo                               0
% 5.97/1.49  fd_cond                                 0
% 5.97/1.49  fd_pseudo_cond                          0
% 5.97/1.49  AC symbols                              0
% 5.97/1.49  
% 5.97/1.49  ------ Schedule dynamic 5 is on 
% 5.97/1.49  
% 5.97/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 5.97/1.49  
% 5.97/1.49  
% 5.97/1.49  ------ 
% 5.97/1.49  Current options:
% 5.97/1.49  ------ 
% 5.97/1.49  
% 5.97/1.49  ------ Input Options
% 5.97/1.49  
% 5.97/1.49  --out_options                           all
% 5.97/1.49  --tptp_safe_out                         true
% 5.97/1.49  --problem_path                          ""
% 5.97/1.49  --include_path                          ""
% 5.97/1.49  --clausifier                            res/vclausify_rel
% 5.97/1.49  --clausifier_options                    --mode clausify
% 5.97/1.49  --stdin                                 false
% 5.97/1.49  --stats_out                             all
% 5.97/1.49  
% 5.97/1.49  ------ General Options
% 5.97/1.49  
% 5.97/1.49  --fof                                   false
% 5.97/1.49  --time_out_real                         305.
% 5.97/1.49  --time_out_virtual                      -1.
% 5.97/1.49  --symbol_type_check                     false
% 5.97/1.49  --clausify_out                          false
% 5.97/1.49  --sig_cnt_out                           false
% 5.97/1.49  --trig_cnt_out                          false
% 5.97/1.49  --trig_cnt_out_tolerance                1.
% 5.97/1.49  --trig_cnt_out_sk_spl                   false
% 5.97/1.49  --abstr_cl_out                          false
% 5.97/1.49  
% 5.97/1.49  ------ Global Options
% 5.97/1.49  
% 5.97/1.49  --schedule                              default
% 5.97/1.49  --add_important_lit                     false
% 5.97/1.49  --prop_solver_per_cl                    1000
% 5.97/1.49  --min_unsat_core                        false
% 5.97/1.49  --soft_assumptions                      false
% 5.97/1.49  --soft_lemma_size                       3
% 5.97/1.49  --prop_impl_unit_size                   0
% 5.97/1.49  --prop_impl_unit                        []
% 5.97/1.49  --share_sel_clauses                     true
% 5.97/1.49  --reset_solvers                         false
% 5.97/1.49  --bc_imp_inh                            [conj_cone]
% 5.97/1.49  --conj_cone_tolerance                   3.
% 5.97/1.49  --extra_neg_conj                        none
% 5.97/1.49  --large_theory_mode                     true
% 5.97/1.49  --prolific_symb_bound                   200
% 5.97/1.49  --lt_threshold                          2000
% 5.97/1.49  --clause_weak_htbl                      true
% 5.97/1.49  --gc_record_bc_elim                     false
% 5.97/1.49  
% 5.97/1.49  ------ Preprocessing Options
% 5.97/1.49  
% 5.97/1.49  --preprocessing_flag                    true
% 5.97/1.49  --time_out_prep_mult                    0.1
% 5.97/1.49  --splitting_mode                        input
% 5.97/1.49  --splitting_grd                         true
% 5.97/1.49  --splitting_cvd                         false
% 5.97/1.49  --splitting_cvd_svl                     false
% 5.97/1.49  --splitting_nvd                         32
% 5.97/1.49  --sub_typing                            true
% 5.97/1.49  --prep_gs_sim                           true
% 5.97/1.49  --prep_unflatten                        true
% 5.97/1.49  --prep_res_sim                          true
% 5.97/1.49  --prep_upred                            true
% 5.97/1.49  --prep_sem_filter                       exhaustive
% 5.97/1.49  --prep_sem_filter_out                   false
% 5.97/1.49  --pred_elim                             true
% 5.97/1.49  --res_sim_input                         true
% 5.97/1.49  --eq_ax_congr_red                       true
% 5.97/1.49  --pure_diseq_elim                       true
% 5.97/1.49  --brand_transform                       false
% 5.97/1.49  --non_eq_to_eq                          false
% 5.97/1.49  --prep_def_merge                        true
% 5.97/1.49  --prep_def_merge_prop_impl              false
% 5.97/1.49  --prep_def_merge_mbd                    true
% 5.97/1.49  --prep_def_merge_tr_red                 false
% 5.97/1.49  --prep_def_merge_tr_cl                  false
% 5.97/1.49  --smt_preprocessing                     true
% 5.97/1.49  --smt_ac_axioms                         fast
% 5.97/1.49  --preprocessed_out                      false
% 5.97/1.49  --preprocessed_stats                    false
% 5.97/1.49  
% 5.97/1.49  ------ Abstraction refinement Options
% 5.97/1.49  
% 5.97/1.49  --abstr_ref                             []
% 5.97/1.49  --abstr_ref_prep                        false
% 5.97/1.49  --abstr_ref_until_sat                   false
% 5.97/1.49  --abstr_ref_sig_restrict                funpre
% 5.97/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 5.97/1.49  --abstr_ref_under                       []
% 5.97/1.49  
% 5.97/1.49  ------ SAT Options
% 5.97/1.49  
% 5.97/1.49  --sat_mode                              false
% 5.97/1.49  --sat_fm_restart_options                ""
% 5.97/1.49  --sat_gr_def                            false
% 5.97/1.49  --sat_epr_types                         true
% 5.97/1.49  --sat_non_cyclic_types                  false
% 5.97/1.49  --sat_finite_models                     false
% 5.97/1.49  --sat_fm_lemmas                         false
% 5.97/1.49  --sat_fm_prep                           false
% 5.97/1.49  --sat_fm_uc_incr                        true
% 5.97/1.49  --sat_out_model                         small
% 5.97/1.49  --sat_out_clauses                       false
% 5.97/1.49  
% 5.97/1.49  ------ QBF Options
% 5.97/1.49  
% 5.97/1.49  --qbf_mode                              false
% 5.97/1.49  --qbf_elim_univ                         false
% 5.97/1.49  --qbf_dom_inst                          none
% 5.97/1.49  --qbf_dom_pre_inst                      false
% 5.97/1.49  --qbf_sk_in                             false
% 5.97/1.49  --qbf_pred_elim                         true
% 5.97/1.49  --qbf_split                             512
% 5.97/1.49  
% 5.97/1.49  ------ BMC1 Options
% 5.97/1.49  
% 5.97/1.49  --bmc1_incremental                      false
% 5.97/1.49  --bmc1_axioms                           reachable_all
% 5.97/1.49  --bmc1_min_bound                        0
% 5.97/1.49  --bmc1_max_bound                        -1
% 5.97/1.49  --bmc1_max_bound_default                -1
% 5.97/1.49  --bmc1_symbol_reachability              true
% 5.97/1.49  --bmc1_property_lemmas                  false
% 5.97/1.49  --bmc1_k_induction                      false
% 5.97/1.49  --bmc1_non_equiv_states                 false
% 5.97/1.49  --bmc1_deadlock                         false
% 5.97/1.49  --bmc1_ucm                              false
% 5.97/1.49  --bmc1_add_unsat_core                   none
% 5.97/1.49  --bmc1_unsat_core_children              false
% 5.97/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 5.97/1.49  --bmc1_out_stat                         full
% 5.97/1.49  --bmc1_ground_init                      false
% 5.97/1.49  --bmc1_pre_inst_next_state              false
% 5.97/1.49  --bmc1_pre_inst_state                   false
% 5.97/1.49  --bmc1_pre_inst_reach_state             false
% 5.97/1.49  --bmc1_out_unsat_core                   false
% 5.97/1.49  --bmc1_aig_witness_out                  false
% 5.97/1.49  --bmc1_verbose                          false
% 5.97/1.49  --bmc1_dump_clauses_tptp                false
% 5.97/1.49  --bmc1_dump_unsat_core_tptp             false
% 5.97/1.49  --bmc1_dump_file                        -
% 5.97/1.49  --bmc1_ucm_expand_uc_limit              128
% 5.97/1.49  --bmc1_ucm_n_expand_iterations          6
% 5.97/1.49  --bmc1_ucm_extend_mode                  1
% 5.97/1.49  --bmc1_ucm_init_mode                    2
% 5.97/1.49  --bmc1_ucm_cone_mode                    none
% 5.97/1.49  --bmc1_ucm_reduced_relation_type        0
% 5.97/1.49  --bmc1_ucm_relax_model                  4
% 5.97/1.49  --bmc1_ucm_full_tr_after_sat            true
% 5.97/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 5.97/1.49  --bmc1_ucm_layered_model                none
% 5.97/1.49  --bmc1_ucm_max_lemma_size               10
% 5.97/1.49  
% 5.97/1.49  ------ AIG Options
% 5.97/1.49  
% 5.97/1.49  --aig_mode                              false
% 5.97/1.49  
% 5.97/1.49  ------ Instantiation Options
% 5.97/1.49  
% 5.97/1.49  --instantiation_flag                    true
% 5.97/1.49  --inst_sos_flag                         false
% 5.97/1.49  --inst_sos_phase                        true
% 5.97/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 5.97/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 5.97/1.49  --inst_lit_sel_side                     none
% 5.97/1.49  --inst_solver_per_active                1400
% 5.97/1.49  --inst_solver_calls_frac                1.
% 5.97/1.49  --inst_passive_queue_type               priority_queues
% 5.97/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 5.97/1.49  --inst_passive_queues_freq              [25;2]
% 5.97/1.49  --inst_dismatching                      true
% 5.97/1.49  --inst_eager_unprocessed_to_passive     true
% 5.97/1.49  --inst_prop_sim_given                   true
% 5.97/1.49  --inst_prop_sim_new                     false
% 5.97/1.49  --inst_subs_new                         false
% 5.97/1.49  --inst_eq_res_simp                      false
% 5.97/1.49  --inst_subs_given                       false
% 5.97/1.49  --inst_orphan_elimination               true
% 5.97/1.49  --inst_learning_loop_flag               true
% 5.97/1.49  --inst_learning_start                   3000
% 5.97/1.49  --inst_learning_factor                  2
% 5.97/1.49  --inst_start_prop_sim_after_learn       3
% 5.97/1.49  --inst_sel_renew                        solver
% 5.97/1.49  --inst_lit_activity_flag                true
% 5.97/1.49  --inst_restr_to_given                   false
% 5.97/1.49  --inst_activity_threshold               500
% 5.97/1.49  --inst_out_proof                        true
% 5.97/1.49  
% 5.97/1.49  ------ Resolution Options
% 5.97/1.49  
% 5.97/1.49  --resolution_flag                       false
% 5.97/1.49  --res_lit_sel                           adaptive
% 5.97/1.49  --res_lit_sel_side                      none
% 5.97/1.49  --res_ordering                          kbo
% 5.97/1.49  --res_to_prop_solver                    active
% 5.97/1.49  --res_prop_simpl_new                    false
% 5.97/1.49  --res_prop_simpl_given                  true
% 5.97/1.49  --res_passive_queue_type                priority_queues
% 5.97/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 5.97/1.49  --res_passive_queues_freq               [15;5]
% 5.97/1.49  --res_forward_subs                      full
% 5.97/1.49  --res_backward_subs                     full
% 5.97/1.49  --res_forward_subs_resolution           true
% 5.97/1.49  --res_backward_subs_resolution          true
% 5.97/1.49  --res_orphan_elimination                true
% 5.97/1.49  --res_time_limit                        2.
% 5.97/1.49  --res_out_proof                         true
% 5.97/1.49  
% 5.97/1.49  ------ Superposition Options
% 5.97/1.49  
% 5.97/1.49  --superposition_flag                    true
% 5.97/1.49  --sup_passive_queue_type                priority_queues
% 5.97/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 5.97/1.49  --sup_passive_queues_freq               [8;1;4]
% 5.97/1.49  --demod_completeness_check              fast
% 5.97/1.49  --demod_use_ground                      true
% 5.97/1.49  --sup_to_prop_solver                    passive
% 5.97/1.49  --sup_prop_simpl_new                    true
% 5.97/1.49  --sup_prop_simpl_given                  true
% 5.97/1.49  --sup_fun_splitting                     false
% 5.97/1.49  --sup_smt_interval                      50000
% 5.97/1.49  
% 5.97/1.49  ------ Superposition Simplification Setup
% 5.97/1.49  
% 5.97/1.49  --sup_indices_passive                   []
% 5.97/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.97/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.97/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.97/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 5.97/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.97/1.49  --sup_full_bw                           [BwDemod]
% 5.97/1.49  --sup_immed_triv                        [TrivRules]
% 5.97/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 5.97/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.97/1.49  --sup_immed_bw_main                     []
% 5.97/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.97/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 5.97/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.97/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.97/1.49  
% 5.97/1.49  ------ Combination Options
% 5.97/1.49  
% 5.97/1.49  --comb_res_mult                         3
% 5.97/1.49  --comb_sup_mult                         2
% 5.97/1.49  --comb_inst_mult                        10
% 5.97/1.49  
% 5.97/1.49  ------ Debug Options
% 5.97/1.49  
% 5.97/1.49  --dbg_backtrace                         false
% 5.97/1.49  --dbg_dump_prop_clauses                 false
% 5.97/1.49  --dbg_dump_prop_clauses_file            -
% 5.97/1.49  --dbg_out_stat                          false
% 5.97/1.49  
% 5.97/1.49  
% 5.97/1.49  
% 5.97/1.49  
% 5.97/1.49  ------ Proving...
% 5.97/1.49  
% 5.97/1.49  
% 5.97/1.49  % SZS status Theorem for theBenchmark.p
% 5.97/1.49  
% 5.97/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 5.97/1.49  
% 5.97/1.49  fof(f14,conjecture,(
% 5.97/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f15,negated_conjecture,(
% 5.97/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 5.97/1.49    inference(negated_conjecture,[],[f14])).
% 5.97/1.49  
% 5.97/1.49  fof(f33,plain,(
% 5.97/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 5.97/1.49    inference(ennf_transformation,[],[f15])).
% 5.97/1.49  
% 5.97/1.49  fof(f34,plain,(
% 5.97/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 5.97/1.49    inference(flattening,[],[f33])).
% 5.97/1.49  
% 5.97/1.49  fof(f51,plain,(
% 5.97/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK8),X3) != sK8 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK8),X2) != X4 | k2_partfun1(X3,X1,sK8,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK8,X3,X1) & v1_funct_1(sK8))) )),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f50,plain,(
% 5.97/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK7,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK7,X5),X2) != sK7 | k2_partfun1(X2,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK7,X2,X1) & v1_funct_1(sK7))) )),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f49,plain,(
% 5.97/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK6),X1,k1_tmap_1(X0,X1,X2,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK6),X1,k1_tmap_1(X0,X1,X2,sK6,X4,X5),X2) != X4 | k2_partfun1(sK6,X1,X5,k9_subset_1(X0,X2,sK6)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,X1))) & v1_funct_2(X5,sK6,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK6) & m1_subset_1(sK6,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK6))) )),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f48,plain,(
% 5.97/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK5,X3),X1,k1_tmap_1(X0,X1,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK5,X3),X1,k1_tmap_1(X0,X1,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,X1,X4,k9_subset_1(X0,sK5,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X4,sK5,X1) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f47,plain,(
% 5.97/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK4,k1_tmap_1(X0,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK4,k1_tmap_1(X0,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))) )),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f46,plain,(
% 5.97/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f52,plain,(
% 5.97/1.49    ((((((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7 | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 5.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f34,f51,f50,f49,f48,f47,f46])).
% 5.97/1.49  
% 5.97/1.49  fof(f87,plain,(
% 5.97/1.49    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f10,axiom,(
% 5.97/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f26,plain,(
% 5.97/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.97/1.49    inference(ennf_transformation,[],[f10])).
% 5.97/1.49  
% 5.97/1.49  fof(f67,plain,(
% 5.97/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.97/1.49    inference(cnf_transformation,[],[f26])).
% 5.97/1.49  
% 5.97/1.49  fof(f9,axiom,(
% 5.97/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f24,plain,(
% 5.97/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 5.97/1.49    inference(ennf_transformation,[],[f9])).
% 5.97/1.49  
% 5.97/1.49  fof(f25,plain,(
% 5.97/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 5.97/1.49    inference(flattening,[],[f24])).
% 5.97/1.49  
% 5.97/1.49  fof(f43,plain,(
% 5.97/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 5.97/1.49    inference(nnf_transformation,[],[f25])).
% 5.97/1.49  
% 5.97/1.49  fof(f65,plain,(
% 5.97/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f43])).
% 5.97/1.49  
% 5.97/1.49  fof(f81,plain,(
% 5.97/1.49    r1_subset_1(sK5,sK6)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f77,plain,(
% 5.97/1.49    ~v1_xboole_0(sK5)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f79,plain,(
% 5.97/1.49    ~v1_xboole_0(sK6)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f3,axiom,(
% 5.97/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f16,plain,(
% 5.97/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 5.97/1.49    inference(rectify,[],[f3])).
% 5.97/1.49  
% 5.97/1.49  fof(f19,plain,(
% 5.97/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 5.97/1.49    inference(ennf_transformation,[],[f16])).
% 5.97/1.49  
% 5.97/1.49  fof(f39,plain,(
% 5.97/1.49    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f40,plain,(
% 5.97/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 5.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f39])).
% 5.97/1.49  
% 5.97/1.49  fof(f56,plain,(
% 5.97/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f40])).
% 5.97/1.49  
% 5.97/1.49  fof(f80,plain,(
% 5.97/1.49    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f6,axiom,(
% 5.97/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f21,plain,(
% 5.97/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 5.97/1.49    inference(ennf_transformation,[],[f6])).
% 5.97/1.49  
% 5.97/1.49  fof(f62,plain,(
% 5.97/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.97/1.49    inference(cnf_transformation,[],[f21])).
% 5.97/1.49  
% 5.97/1.49  fof(f5,axiom,(
% 5.97/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f61,plain,(
% 5.97/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.97/1.49    inference(cnf_transformation,[],[f5])).
% 5.97/1.49  
% 5.97/1.49  fof(f91,plain,(
% 5.97/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.97/1.49    inference(definition_unfolding,[],[f62,f61])).
% 5.97/1.49  
% 5.97/1.49  fof(f4,axiom,(
% 5.97/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f17,plain,(
% 5.97/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 5.97/1.49    inference(rectify,[],[f4])).
% 5.97/1.49  
% 5.97/1.49  fof(f20,plain,(
% 5.97/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 5.97/1.49    inference(ennf_transformation,[],[f17])).
% 5.97/1.49  
% 5.97/1.49  fof(f41,plain,(
% 5.97/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 5.97/1.49    introduced(choice_axiom,[])).
% 5.97/1.49  
% 5.97/1.49  fof(f42,plain,(
% 5.97/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 5.97/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f41])).
% 5.97/1.49  
% 5.97/1.49  fof(f60,plain,(
% 5.97/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 5.97/1.49    inference(cnf_transformation,[],[f42])).
% 5.97/1.49  
% 5.97/1.49  fof(f89,plain,(
% 5.97/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 5.97/1.49    inference(definition_unfolding,[],[f60,f61])).
% 5.97/1.49  
% 5.97/1.49  fof(f8,axiom,(
% 5.97/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f23,plain,(
% 5.97/1.49    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 5.97/1.49    inference(ennf_transformation,[],[f8])).
% 5.97/1.49  
% 5.97/1.49  fof(f64,plain,(
% 5.97/1.49    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f23])).
% 5.97/1.49  
% 5.97/1.49  fof(f11,axiom,(
% 5.97/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f27,plain,(
% 5.97/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 5.97/1.49    inference(ennf_transformation,[],[f11])).
% 5.97/1.49  
% 5.97/1.49  fof(f28,plain,(
% 5.97/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 5.97/1.49    inference(flattening,[],[f27])).
% 5.97/1.49  
% 5.97/1.49  fof(f68,plain,(
% 5.97/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f28])).
% 5.97/1.49  
% 5.97/1.49  fof(f85,plain,(
% 5.97/1.49    v1_funct_1(sK8)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f84,plain,(
% 5.97/1.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f82,plain,(
% 5.97/1.49    v1_funct_1(sK7)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f12,axiom,(
% 5.97/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f29,plain,(
% 5.97/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.97/1.49    inference(ennf_transformation,[],[f12])).
% 5.97/1.49  
% 5.97/1.49  fof(f30,plain,(
% 5.97/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.97/1.49    inference(flattening,[],[f29])).
% 5.97/1.49  
% 5.97/1.49  fof(f44,plain,(
% 5.97/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.97/1.49    inference(nnf_transformation,[],[f30])).
% 5.97/1.49  
% 5.97/1.49  fof(f45,plain,(
% 5.97/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.97/1.49    inference(flattening,[],[f44])).
% 5.97/1.49  
% 5.97/1.49  fof(f69,plain,(
% 5.97/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f45])).
% 5.97/1.49  
% 5.97/1.49  fof(f95,plain,(
% 5.97/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(equality_resolution,[],[f69])).
% 5.97/1.49  
% 5.97/1.49  fof(f13,axiom,(
% 5.97/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f31,plain,(
% 5.97/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 5.97/1.49    inference(ennf_transformation,[],[f13])).
% 5.97/1.49  
% 5.97/1.49  fof(f32,plain,(
% 5.97/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 5.97/1.49    inference(flattening,[],[f31])).
% 5.97/1.49  
% 5.97/1.49  fof(f72,plain,(
% 5.97/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f32])).
% 5.97/1.49  
% 5.97/1.49  fof(f73,plain,(
% 5.97/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f32])).
% 5.97/1.49  
% 5.97/1.49  fof(f74,plain,(
% 5.97/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f32])).
% 5.97/1.49  
% 5.97/1.49  fof(f7,axiom,(
% 5.97/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 5.97/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 5.97/1.49  
% 5.97/1.49  fof(f22,plain,(
% 5.97/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 5.97/1.49    inference(ennf_transformation,[],[f7])).
% 5.97/1.49  
% 5.97/1.49  fof(f63,plain,(
% 5.97/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f22])).
% 5.97/1.49  
% 5.97/1.49  fof(f76,plain,(
% 5.97/1.49    ~v1_xboole_0(sK4)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f83,plain,(
% 5.97/1.49    v1_funct_2(sK7,sK5,sK4)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f86,plain,(
% 5.97/1.49    v1_funct_2(sK8,sK6,sK4)),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f70,plain,(
% 5.97/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(cnf_transformation,[],[f45])).
% 5.97/1.49  
% 5.97/1.49  fof(f94,plain,(
% 5.97/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.97/1.49    inference(equality_resolution,[],[f70])).
% 5.97/1.49  
% 5.97/1.49  fof(f88,plain,(
% 5.97/1.49    k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7 | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  fof(f78,plain,(
% 5.97/1.49    m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 5.97/1.49    inference(cnf_transformation,[],[f52])).
% 5.97/1.49  
% 5.97/1.49  cnf(c_22,negated_conjecture,
% 5.97/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 5.97/1.49      inference(cnf_transformation,[],[f87]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_654,negated_conjecture,
% 5.97/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1283,plain,
% 5.97/1.49      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_654]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_13,plain,
% 5.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.49      | v1_relat_1(X0) ),
% 5.97/1.49      inference(cnf_transformation,[],[f67]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_661,plain,
% 5.97/1.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 5.97/1.49      | v1_relat_1(X0_55) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1277,plain,
% 5.97/1.49      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 5.97/1.49      | v1_relat_1(X0_55) = iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_2129,plain,
% 5.97/1.49      ( v1_relat_1(sK8) = iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_1283,c_1277]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_12,plain,
% 5.97/1.49      ( ~ r1_subset_1(X0,X1)
% 5.97/1.49      | r1_xboole_0(X0,X1)
% 5.97/1.49      | v1_xboole_0(X0)
% 5.97/1.49      | v1_xboole_0(X1) ),
% 5.97/1.49      inference(cnf_transformation,[],[f65]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_28,negated_conjecture,
% 5.97/1.49      ( r1_subset_1(sK5,sK6) ),
% 5.97/1.49      inference(cnf_transformation,[],[f81]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_394,plain,
% 5.97/1.49      ( r1_xboole_0(X0,X1)
% 5.97/1.49      | v1_xboole_0(X0)
% 5.97/1.49      | v1_xboole_0(X1)
% 5.97/1.49      | sK6 != X1
% 5.97/1.49      | sK5 != X0 ),
% 5.97/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_395,plain,
% 5.97/1.49      ( r1_xboole_0(sK5,sK6) | v1_xboole_0(sK6) | v1_xboole_0(sK5) ),
% 5.97/1.49      inference(unflattening,[status(thm)],[c_394]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_32,negated_conjecture,
% 5.97/1.49      ( ~ v1_xboole_0(sK5) ),
% 5.97/1.49      inference(cnf_transformation,[],[f77]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_30,negated_conjecture,
% 5.97/1.49      ( ~ v1_xboole_0(sK6) ),
% 5.97/1.49      inference(cnf_transformation,[],[f79]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_397,plain,
% 5.97/1.49      ( r1_xboole_0(sK5,sK6) ),
% 5.97/1.49      inference(global_propositional_subsumption,
% 5.97/1.49                [status(thm)],
% 5.97/1.49                [c_395,c_32,c_30]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_640,plain,
% 5.97/1.49      ( r1_xboole_0(sK5,sK6) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_397]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1297,plain,
% 5.97/1.49      ( r1_xboole_0(sK5,sK6) = iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_5,plain,
% 5.97/1.49      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 5.97/1.49      inference(cnf_transformation,[],[f56]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_667,plain,
% 5.97/1.49      ( r1_xboole_0(X0_55,X1_55) | r2_hidden(sK1(X0_55,X1_55),X0_55) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1271,plain,
% 5.97/1.49      ( r1_xboole_0(X0_55,X1_55) = iProver_top
% 5.97/1.49      | r2_hidden(sK1(X0_55,X1_55),X0_55) = iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_29,negated_conjecture,
% 5.97/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 5.97/1.49      inference(cnf_transformation,[],[f80]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_648,negated_conjecture,
% 5.97/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1289,plain,
% 5.97/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_8,plain,
% 5.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 5.97/1.49      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 5.97/1.49      inference(cnf_transformation,[],[f91]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_664,plain,
% 5.97/1.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 5.97/1.49      | k4_xboole_0(X2_55,k4_xboole_0(X2_55,X0_55)) = k9_subset_1(X1_55,X2_55,X0_55) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1274,plain,
% 5.97/1.49      ( k4_xboole_0(X0_55,k4_xboole_0(X0_55,X1_55)) = k9_subset_1(X2_55,X0_55,X1_55)
% 5.97/1.49      | m1_subset_1(X1_55,k1_zfmisc_1(X2_55)) != iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_2215,plain,
% 5.97/1.49      ( k4_xboole_0(X0_55,k4_xboole_0(X0_55,sK6)) = k9_subset_1(sK3,X0_55,sK6) ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_1289,c_1274]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_6,plain,
% 5.97/1.49      ( ~ r1_xboole_0(X0,X1)
% 5.97/1.49      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 5.97/1.49      inference(cnf_transformation,[],[f89]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_666,plain,
% 5.97/1.49      ( ~ r1_xboole_0(X0_55,X1_55)
% 5.97/1.49      | ~ r2_hidden(X0_57,k4_xboole_0(X0_55,k4_xboole_0(X0_55,X1_55))) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1272,plain,
% 5.97/1.49      ( r1_xboole_0(X0_55,X1_55) != iProver_top
% 5.97/1.49      | r2_hidden(X0_57,k4_xboole_0(X0_55,k4_xboole_0(X0_55,X1_55))) != iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_2719,plain,
% 5.97/1.49      ( r1_xboole_0(X0_55,sK6) != iProver_top
% 5.97/1.49      | r2_hidden(X0_57,k9_subset_1(sK3,X0_55,sK6)) != iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_2215,c_1272]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_2930,plain,
% 5.97/1.49      ( r1_xboole_0(X0_55,sK6) != iProver_top
% 5.97/1.49      | r1_xboole_0(k9_subset_1(sK3,X0_55,sK6),X1_55) = iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_1271,c_2719]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_10,plain,
% 5.97/1.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 5.97/1.49      | ~ v1_relat_1(X1)
% 5.97/1.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 5.97/1.49      inference(cnf_transformation,[],[f64]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_662,plain,
% 5.97/1.49      ( ~ r1_xboole_0(X0_55,k1_relat_1(X1_55))
% 5.97/1.49      | ~ v1_relat_1(X1_55)
% 5.97/1.49      | k7_relat_1(X1_55,X0_55) = k1_xboole_0 ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1276,plain,
% 5.97/1.49      ( k7_relat_1(X0_55,X1_55) = k1_xboole_0
% 5.97/1.49      | r1_xboole_0(X1_55,k1_relat_1(X0_55)) != iProver_top
% 5.97/1.49      | v1_relat_1(X0_55) != iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_5053,plain,
% 5.97/1.49      ( k7_relat_1(X0_55,k9_subset_1(sK3,X1_55,sK6)) = k1_xboole_0
% 5.97/1.49      | r1_xboole_0(X1_55,sK6) != iProver_top
% 5.97/1.49      | v1_relat_1(X0_55) != iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_2930,c_1276]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_11371,plain,
% 5.97/1.49      ( k7_relat_1(X0_55,k9_subset_1(sK3,sK5,sK6)) = k1_xboole_0
% 5.97/1.49      | v1_relat_1(X0_55) != iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_1297,c_5053]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_11855,plain,
% 5.97/1.49      ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k1_xboole_0 ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_2129,c_11371]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_14,plain,
% 5.97/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.49      | ~ v1_funct_1(X0)
% 5.97/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 5.97/1.49      inference(cnf_transformation,[],[f68]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_660,plain,
% 5.97/1.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 5.97/1.49      | ~ v1_funct_1(X0_55)
% 5.97/1.49      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1278,plain,
% 5.97/1.49      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 5.97/1.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 5.97/1.49      | v1_funct_1(X2_55) != iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_3254,plain,
% 5.97/1.49      ( k2_partfun1(sK6,sK4,sK8,X0_55) = k7_relat_1(sK8,X0_55)
% 5.97/1.49      | v1_funct_1(sK8) != iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_1283,c_1278]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_24,negated_conjecture,
% 5.97/1.49      ( v1_funct_1(sK8) ),
% 5.97/1.49      inference(cnf_transformation,[],[f85]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1704,plain,
% 5.97/1.49      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 5.97/1.49      | ~ v1_funct_1(sK8)
% 5.97/1.49      | k2_partfun1(X0_55,X1_55,sK8,X2_55) = k7_relat_1(sK8,X2_55) ),
% 5.97/1.49      inference(instantiation,[status(thm)],[c_660]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1863,plain,
% 5.97/1.49      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
% 5.97/1.49      | ~ v1_funct_1(sK8)
% 5.97/1.49      | k2_partfun1(sK6,sK4,sK8,X0_55) = k7_relat_1(sK8,X0_55) ),
% 5.97/1.49      inference(instantiation,[status(thm)],[c_1704]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_3526,plain,
% 5.97/1.49      ( k2_partfun1(sK6,sK4,sK8,X0_55) = k7_relat_1(sK8,X0_55) ),
% 5.97/1.49      inference(global_propositional_subsumption,
% 5.97/1.49                [status(thm)],
% 5.97/1.49                [c_3254,c_24,c_22,c_1863]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_25,negated_conjecture,
% 5.97/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 5.97/1.49      inference(cnf_transformation,[],[f84]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_651,negated_conjecture,
% 5.97/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
% 5.97/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1286,plain,
% 5.97/1.49      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 5.97/1.49      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_3255,plain,
% 5.97/1.49      ( k2_partfun1(sK5,sK4,sK7,X0_55) = k7_relat_1(sK7,X0_55)
% 5.97/1.49      | v1_funct_1(sK7) != iProver_top ),
% 5.97/1.49      inference(superposition,[status(thm)],[c_1286,c_1278]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_27,negated_conjecture,
% 5.97/1.49      ( v1_funct_1(sK7) ),
% 5.97/1.49      inference(cnf_transformation,[],[f82]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1709,plain,
% 5.97/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 5.97/1.49      | ~ v1_funct_1(sK7)
% 5.97/1.49      | k2_partfun1(X0_55,X1_55,sK7,X2_55) = k7_relat_1(sK7,X2_55) ),
% 5.97/1.49      inference(instantiation,[status(thm)],[c_660]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_1868,plain,
% 5.97/1.49      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
% 5.97/1.49      | ~ v1_funct_1(sK7)
% 5.97/1.49      | k2_partfun1(sK5,sK4,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
% 5.97/1.49      inference(instantiation,[status(thm)],[c_1709]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_3616,plain,
% 5.97/1.49      ( k2_partfun1(sK5,sK4,sK7,X0_55) = k7_relat_1(sK7,X0_55) ),
% 5.97/1.49      inference(global_propositional_subsumption,
% 5.97/1.49                [status(thm)],
% 5.97/1.49                [c_3255,c_27,c_25,c_1868]) ).
% 5.97/1.49  
% 5.97/1.49  cnf(c_17,plain,
% 5.97/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.49      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 5.97/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1)
% 5.97/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 5.97/1.50      inference(cnf_transformation,[],[f95]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_20,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1) ),
% 5.97/1.50      inference(cnf_transformation,[],[f72]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_19,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1) ),
% 5.97/1.50      inference(cnf_transformation,[],[f73]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_18,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1) ),
% 5.97/1.50      inference(cnf_transformation,[],[f74]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_186,plain,
% 5.97/1.50      ( ~ v1_funct_1(X3)
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1)
% 5.97/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 5.97/1.50      inference(global_propositional_subsumption,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_17,c_20,c_19,c_18]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_187,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | v1_xboole_0(X1)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 5.97/1.50      inference(renaming,[status(thm)],[c_186]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_642,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 5.97/1.50      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 5.97/1.50      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 5.97/1.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 5.97/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 5.97/1.50      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 5.97/1.50      | ~ v1_funct_1(X0_55)
% 5.97/1.50      | ~ v1_funct_1(X3_55)
% 5.97/1.50      | v1_xboole_0(X1_55)
% 5.97/1.50      | v1_xboole_0(X2_55)
% 5.97/1.50      | v1_xboole_0(X4_55)
% 5.97/1.50      | v1_xboole_0(X5_55)
% 5.97/1.50      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
% 5.97/1.50      inference(subtyping,[status(esa)],[c_187]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_1295,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
% 5.97/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 5.97/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 5.97/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 5.97/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 5.97/1.50      | v1_funct_1(X2_55) != iProver_top
% 5.97/1.50      | v1_funct_1(X5_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X3_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X4_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X1_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_9,plain,
% 5.97/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 5.97/1.50      | ~ v1_xboole_0(X1)
% 5.97/1.50      | v1_xboole_0(X0) ),
% 5.97/1.50      inference(cnf_transformation,[],[f63]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_663,plain,
% 5.97/1.50      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 5.97/1.50      | ~ v1_xboole_0(X1_55)
% 5.97/1.50      | v1_xboole_0(X0_55) ),
% 5.97/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_1275,plain,
% 5.97/1.50      ( m1_subset_1(X0_55,k1_zfmisc_1(X1_55)) != iProver_top
% 5.97/1.50      | v1_xboole_0(X1_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_1482,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X0_55) = X2_55
% 5.97/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 5.97/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 5.97/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 5.97/1.50      | v1_funct_1(X5_55) != iProver_top
% 5.97/1.50      | v1_funct_1(X2_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X1_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X4_55) = iProver_top ),
% 5.97/1.50      inference(forward_subsumption_resolution,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_1295,c_1275]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_6388,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),sK5) = sK7
% 5.97/1.50      | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
% 5.97/1.50      | v1_funct_2(sK7,sK5,sK4) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | v1_funct_1(X1_55) != iProver_top
% 5.97/1.50      | v1_funct_1(sK7) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(sK4) = iProver_top
% 5.97/1.50      | v1_xboole_0(sK5) = iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_3616,c_1482]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_33,negated_conjecture,
% 5.97/1.50      ( ~ v1_xboole_0(sK4) ),
% 5.97/1.50      inference(cnf_transformation,[],[f76]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_36,plain,
% 5.97/1.50      ( v1_xboole_0(sK4) != iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_37,plain,
% 5.97/1.50      ( v1_xboole_0(sK5) != iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_42,plain,
% 5.97/1.50      ( v1_funct_1(sK7) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_26,negated_conjecture,
% 5.97/1.50      ( v1_funct_2(sK7,sK5,sK4) ),
% 5.97/1.50      inference(cnf_transformation,[],[f83]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_43,plain,
% 5.97/1.50      ( v1_funct_2(sK7,sK5,sK4) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_44,plain,
% 5.97/1.50      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_8499,plain,
% 5.97/1.50      ( v1_funct_1(X1_55) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
% 5.97/1.50      | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),sK5) = sK7
% 5.97/1.50      | k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(global_propositional_subsumption,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_6388,c_36,c_37,c_42,c_43,c_44]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_8500,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),sK5) = sK7
% 5.97/1.50      | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | v1_funct_1(X1_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(renaming,[status(thm)],[c_8499]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_8513,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK5) = sK7
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
% 5.97/1.50      | v1_funct_2(sK8,sK6,sK4) != iProver_top
% 5.97/1.50      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 5.97/1.50      | v1_funct_1(sK8) != iProver_top
% 5.97/1.50      | v1_xboole_0(sK6) = iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_3526,c_8500]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_39,plain,
% 5.97/1.50      ( v1_xboole_0(sK6) != iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_45,plain,
% 5.97/1.50      ( v1_funct_1(sK8) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_23,negated_conjecture,
% 5.97/1.50      ( v1_funct_2(sK8,sK6,sK4) ),
% 5.97/1.50      inference(cnf_transformation,[],[f86]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_46,plain,
% 5.97/1.50      ( v1_funct_2(sK8,sK6,sK4) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_47,plain,
% 5.97/1.50      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_9098,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK5) = sK7
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
% 5.97/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top ),
% 5.97/1.50      inference(global_propositional_subsumption,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_8513,c_39,c_45,c_46,c_47]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_11926,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) = sK7
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k1_xboole_0
% 5.97/1.50      | m1_subset_1(sK6,k1_zfmisc_1(sK3)) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(sK3)) != iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_11855,c_9098]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_16,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1)
% 5.97/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 5.97/1.50      inference(cnf_transformation,[],[f94]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_193,plain,
% 5.97/1.50      ( ~ v1_funct_1(X3)
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X1)
% 5.97/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 5.97/1.50      inference(global_propositional_subsumption,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_16,c_20,c_19,c_18]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_194,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 5.97/1.50      | ~ v1_funct_2(X3,X4,X2)
% 5.97/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.97/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.97/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.97/1.50      | ~ v1_funct_1(X0)
% 5.97/1.50      | ~ v1_funct_1(X3)
% 5.97/1.50      | v1_xboole_0(X1)
% 5.97/1.50      | v1_xboole_0(X2)
% 5.97/1.50      | v1_xboole_0(X4)
% 5.97/1.50      | v1_xboole_0(X5)
% 5.97/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 5.97/1.50      inference(renaming,[status(thm)],[c_193]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_641,plain,
% 5.97/1.50      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 5.97/1.50      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 5.97/1.50      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 5.97/1.50      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 5.97/1.50      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 5.97/1.50      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 5.97/1.50      | ~ v1_funct_1(X0_55)
% 5.97/1.50      | ~ v1_funct_1(X3_55)
% 5.97/1.50      | v1_xboole_0(X1_55)
% 5.97/1.50      | v1_xboole_0(X2_55)
% 5.97/1.50      | v1_xboole_0(X4_55)
% 5.97/1.50      | v1_xboole_0(X5_55)
% 5.97/1.50      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
% 5.97/1.50      inference(subtyping,[status(esa)],[c_194]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_1296,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
% 5.97/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 5.97/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 5.97/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 5.97/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 5.97/1.50      | v1_funct_1(X2_55) != iProver_top
% 5.97/1.50      | v1_funct_1(X5_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X3_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X4_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X1_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_1510,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X0_55,X4_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X0_55,X4_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X3_55,X0_55,X4_55),X1_55,k1_tmap_1(X3_55,X1_55,X0_55,X4_55,X2_55,X5_55),X4_55) = X5_55
% 5.97/1.50      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 5.97/1.50      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 5.97/1.50      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 5.97/1.50      | v1_funct_1(X5_55) != iProver_top
% 5.97/1.50      | v1_funct_1(X2_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X1_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(X4_55) = iProver_top ),
% 5.97/1.50      inference(forward_subsumption_resolution,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_1296,c_1275]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_8676,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),X0_55) = X1_55
% 5.97/1.50      | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
% 5.97/1.50      | v1_funct_2(sK7,sK5,sK4) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | v1_funct_1(X1_55) != iProver_top
% 5.97/1.50      | v1_funct_1(sK7) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top
% 5.97/1.50      | v1_xboole_0(sK4) = iProver_top
% 5.97/1.50      | v1_xboole_0(sK5) = iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_3616,c_1510]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_9968,plain,
% 5.97/1.50      ( v1_funct_1(X1_55) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
% 5.97/1.50      | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),X0_55) = X1_55
% 5.97/1.50      | k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(global_propositional_subsumption,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_8676,c_36,c_37,c_42,c_43,c_44]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_9969,plain,
% 5.97/1.50      ( k2_partfun1(X0_55,sK4,X1_55,k9_subset_1(X2_55,sK5,X0_55)) != k7_relat_1(sK7,k9_subset_1(X2_55,sK5,X0_55))
% 5.97/1.50      | k2_partfun1(k4_subset_1(X2_55,sK5,X0_55),sK4,k1_tmap_1(X2_55,sK4,sK5,X0_55,sK7,X1_55),X0_55) = X1_55
% 5.97/1.50      | v1_funct_2(X1_55,X0_55,sK4) != iProver_top
% 5.97/1.50      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X2_55)) != iProver_top
% 5.97/1.50      | v1_funct_1(X1_55) != iProver_top
% 5.97/1.50      | v1_xboole_0(X0_55) = iProver_top ),
% 5.97/1.50      inference(renaming,[status(thm)],[c_9968]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_9982,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK6) = sK8
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
% 5.97/1.50      | v1_funct_2(sK8,sK6,sK4) != iProver_top
% 5.97/1.50      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) != iProver_top
% 5.97/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top
% 5.97/1.50      | v1_funct_1(sK8) != iProver_top
% 5.97/1.50      | v1_xboole_0(sK6) = iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_3526,c_9969]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_10153,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(X0_55,sK5,sK6),sK4,k1_tmap_1(X0_55,sK4,sK5,sK6,sK7,sK8),sK6) = sK8
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(X0_55,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(X0_55,sK5,sK6))
% 5.97/1.50      | m1_subset_1(sK6,k1_zfmisc_1(X0_55)) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(X0_55)) != iProver_top ),
% 5.97/1.50      inference(global_propositional_subsumption,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_9982,c_39,c_45,c_46,c_47]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_11925,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) = sK8
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k1_xboole_0
% 5.97/1.50      | m1_subset_1(sK6,k1_zfmisc_1(sK3)) != iProver_top
% 5.97/1.50      | m1_subset_1(sK5,k1_zfmisc_1(sK3)) != iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_11855,c_10153]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_21,negated_conjecture,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
% 5.97/1.50      | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
% 5.97/1.50      | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
% 5.97/1.50      inference(cnf_transformation,[],[f88]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_655,negated_conjecture,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
% 5.97/1.50      | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
% 5.97/1.50      | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
% 5.97/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_3530,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
% 5.97/1.50      | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
% 5.97/1.50      | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) ),
% 5.97/1.50      inference(demodulation,[status(thm)],[c_3526,c_655]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_3620,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
% 5.97/1.50      | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) ),
% 5.97/1.50      inference(demodulation,[status(thm)],[c_3616,c_3530]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_11924,plain,
% 5.97/1.50      ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) != sK8
% 5.97/1.50      | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) != sK7
% 5.97/1.50      | k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) != k1_xboole_0 ),
% 5.97/1.50      inference(demodulation,[status(thm)],[c_11855,c_3620]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_2130,plain,
% 5.97/1.50      ( v1_relat_1(sK7) = iProver_top ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_1286,c_1277]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_11856,plain,
% 5.97/1.50      ( k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) = k1_xboole_0 ),
% 5.97/1.50      inference(superposition,[status(thm)],[c_2130,c_11371]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_40,plain,
% 5.97/1.50      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_31,negated_conjecture,
% 5.97/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
% 5.97/1.50      inference(cnf_transformation,[],[f78]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(c_38,plain,
% 5.97/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(sK3)) = iProver_top ),
% 5.97/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 5.97/1.50  
% 5.97/1.50  cnf(contradiction,plain,
% 5.97/1.50      ( $false ),
% 5.97/1.50      inference(minisat,
% 5.97/1.50                [status(thm)],
% 5.97/1.50                [c_11926,c_11925,c_11924,c_11856,c_40,c_38]) ).
% 5.97/1.50  
% 5.97/1.50  
% 5.97/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 5.97/1.50  
% 5.97/1.50  ------                               Statistics
% 5.97/1.50  
% 5.97/1.50  ------ General
% 5.97/1.50  
% 5.97/1.50  abstr_ref_over_cycles:                  0
% 5.97/1.50  abstr_ref_under_cycles:                 0
% 5.97/1.50  gc_basic_clause_elim:                   0
% 5.97/1.50  forced_gc_time:                         0
% 5.97/1.50  parsing_time:                           0.013
% 5.97/1.50  unif_index_cands_time:                  0.
% 5.97/1.50  unif_index_add_time:                    0.
% 5.97/1.50  orderings_time:                         0.
% 5.97/1.50  out_proof_time:                         0.013
% 5.97/1.50  total_time:                             0.628
% 5.97/1.50  num_of_symbols:                         61
% 5.97/1.50  num_of_terms:                           29767
% 5.97/1.50  
% 5.97/1.50  ------ Preprocessing
% 5.97/1.50  
% 5.97/1.50  num_of_splits:                          0
% 5.97/1.50  num_of_split_atoms:                     0
% 5.97/1.50  num_of_reused_defs:                     0
% 5.97/1.50  num_eq_ax_congr_red:                    31
% 5.97/1.50  num_of_sem_filtered_clauses:            1
% 5.97/1.50  num_of_subtypes:                        3
% 5.97/1.50  monotx_restored_types:                  0
% 5.97/1.50  sat_num_of_epr_types:                   0
% 5.97/1.50  sat_num_of_non_cyclic_types:            0
% 5.97/1.50  sat_guarded_non_collapsed_types:        1
% 5.97/1.50  num_pure_diseq_elim:                    0
% 5.97/1.50  simp_replaced_by:                       0
% 5.97/1.50  res_preprocessed:                       169
% 5.97/1.50  prep_upred:                             0
% 5.97/1.50  prep_unflattend:                        4
% 5.97/1.50  smt_new_axioms:                         0
% 5.97/1.50  pred_elim_cands:                        7
% 5.97/1.50  pred_elim:                              1
% 5.97/1.50  pred_elim_cl:                           2
% 5.97/1.50  pred_elim_cycles:                       4
% 5.97/1.50  merged_defs:                            0
% 5.97/1.50  merged_defs_ncl:                        0
% 5.97/1.50  bin_hyper_res:                          0
% 5.97/1.50  prep_cycles:                            4
% 5.97/1.50  pred_elim_time:                         0.002
% 5.97/1.50  splitting_time:                         0.
% 5.97/1.50  sem_filter_time:                        0.
% 5.97/1.50  monotx_time:                            0.
% 5.97/1.50  subtype_inf_time:                       0.001
% 5.97/1.50  
% 5.97/1.50  ------ Problem properties
% 5.97/1.50  
% 5.97/1.50  clauses:                                33
% 5.97/1.50  conjectures:                            13
% 5.97/1.50  epr:                                    12
% 5.97/1.50  horn:                                   23
% 5.97/1.50  ground:                                 14
% 5.97/1.50  unary:                                  13
% 5.97/1.50  binary:                                 9
% 5.97/1.50  lits:                                   130
% 5.97/1.50  lits_eq:                                12
% 5.97/1.50  fd_pure:                                0
% 5.97/1.50  fd_pseudo:                              0
% 5.97/1.50  fd_cond:                                0
% 5.97/1.50  fd_pseudo_cond:                         0
% 5.97/1.50  ac_symbols:                             0
% 5.97/1.50  
% 5.97/1.50  ------ Propositional Solver
% 5.97/1.50  
% 5.97/1.50  prop_solver_calls:                      27
% 5.97/1.50  prop_fast_solver_calls:                 2096
% 5.97/1.50  smt_solver_calls:                       0
% 5.97/1.50  smt_fast_solver_calls:                  0
% 5.97/1.50  prop_num_of_clauses:                    5660
% 5.97/1.50  prop_preprocess_simplified:             10531
% 5.97/1.50  prop_fo_subsumed:                       85
% 5.97/1.50  prop_solver_time:                       0.
% 5.97/1.50  smt_solver_time:                        0.
% 5.97/1.50  smt_fast_solver_time:                   0.
% 5.97/1.50  prop_fast_solver_time:                  0.
% 5.97/1.50  prop_unsat_core_time:                   0.
% 5.97/1.50  
% 5.97/1.50  ------ QBF
% 5.97/1.50  
% 5.97/1.50  qbf_q_res:                              0
% 5.97/1.50  qbf_num_tautologies:                    0
% 5.97/1.50  qbf_prep_cycles:                        0
% 5.97/1.50  
% 5.97/1.50  ------ BMC1
% 5.97/1.50  
% 5.97/1.50  bmc1_current_bound:                     -1
% 5.97/1.50  bmc1_last_solved_bound:                 -1
% 5.97/1.50  bmc1_unsat_core_size:                   -1
% 5.97/1.50  bmc1_unsat_core_parents_size:           -1
% 5.97/1.50  bmc1_merge_next_fun:                    0
% 5.97/1.50  bmc1_unsat_core_clauses_time:           0.
% 5.97/1.50  
% 5.97/1.50  ------ Instantiation
% 5.97/1.50  
% 5.97/1.50  inst_num_of_clauses:                    1329
% 5.97/1.50  inst_num_in_passive:                    214
% 5.97/1.50  inst_num_in_active:                     697
% 5.97/1.50  inst_num_in_unprocessed:                418
% 5.97/1.50  inst_num_of_loops:                      720
% 5.97/1.50  inst_num_of_learning_restarts:          0
% 5.97/1.50  inst_num_moves_active_passive:          19
% 5.97/1.50  inst_lit_activity:                      0
% 5.97/1.50  inst_lit_activity_moves:                0
% 5.97/1.50  inst_num_tautologies:                   0
% 5.97/1.50  inst_num_prop_implied:                  0
% 5.97/1.50  inst_num_existing_simplified:           0
% 5.97/1.50  inst_num_eq_res_simplified:             0
% 5.97/1.50  inst_num_child_elim:                    0
% 5.97/1.50  inst_num_of_dismatching_blockings:      198
% 5.97/1.50  inst_num_of_non_proper_insts:           977
% 5.97/1.50  inst_num_of_duplicates:                 0
% 5.97/1.50  inst_inst_num_from_inst_to_res:         0
% 5.97/1.50  inst_dismatching_checking_time:         0.
% 5.97/1.50  
% 5.97/1.50  ------ Resolution
% 5.97/1.50  
% 5.97/1.50  res_num_of_clauses:                     0
% 5.97/1.50  res_num_in_passive:                     0
% 5.97/1.50  res_num_in_active:                      0
% 5.97/1.50  res_num_of_loops:                       173
% 5.97/1.50  res_forward_subset_subsumed:            35
% 5.97/1.50  res_backward_subset_subsumed:           0
% 5.97/1.50  res_forward_subsumed:                   0
% 5.97/1.50  res_backward_subsumed:                  0
% 5.97/1.50  res_forward_subsumption_resolution:     0
% 5.97/1.50  res_backward_subsumption_resolution:    0
% 5.97/1.50  res_clause_to_clause_subsumption:       858
% 5.97/1.50  res_orphan_elimination:                 0
% 5.97/1.50  res_tautology_del:                      44
% 5.97/1.50  res_num_eq_res_simplified:              0
% 5.97/1.50  res_num_sel_changes:                    0
% 5.97/1.50  res_moves_from_active_to_pass:          0
% 5.97/1.50  
% 5.97/1.50  ------ Superposition
% 5.97/1.50  
% 5.97/1.50  sup_time_total:                         0.
% 5.97/1.50  sup_time_generating:                    0.
% 5.97/1.50  sup_time_sim_full:                      0.
% 5.97/1.50  sup_time_sim_immed:                     0.
% 5.97/1.50  
% 5.97/1.50  sup_num_of_clauses:                     216
% 5.97/1.50  sup_num_in_active:                      140
% 5.97/1.50  sup_num_in_passive:                     76
% 5.97/1.50  sup_num_of_loops:                       142
% 5.97/1.50  sup_fw_superposition:                   232
% 5.97/1.50  sup_bw_superposition:                   98
% 5.97/1.50  sup_immediate_simplified:               54
% 5.97/1.50  sup_given_eliminated:                   0
% 5.97/1.50  comparisons_done:                       0
% 5.97/1.50  comparisons_avoided:                    0
% 5.97/1.50  
% 5.97/1.50  ------ Simplifications
% 5.97/1.50  
% 5.97/1.50  
% 5.97/1.50  sim_fw_subset_subsumed:                 4
% 5.97/1.50  sim_bw_subset_subsumed:                 0
% 5.97/1.50  sim_fw_subsumed:                        49
% 5.97/1.50  sim_bw_subsumed:                        0
% 5.97/1.50  sim_fw_subsumption_res:                 6
% 5.97/1.50  sim_bw_subsumption_res:                 0
% 5.97/1.50  sim_tautology_del:                      15
% 5.97/1.50  sim_eq_tautology_del:                   0
% 5.97/1.50  sim_eq_res_simp:                        0
% 5.97/1.50  sim_fw_demodulated:                     2
% 5.97/1.50  sim_bw_demodulated:                     3
% 5.97/1.50  sim_light_normalised:                   0
% 5.97/1.50  sim_joinable_taut:                      0
% 5.97/1.50  sim_joinable_simp:                      0
% 5.97/1.50  sim_ac_normalised:                      0
% 5.97/1.50  sim_smt_subsumption:                    0
% 5.97/1.50  
%------------------------------------------------------------------------------
