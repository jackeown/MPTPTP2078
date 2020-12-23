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
% DateTime   : Thu Dec  3 12:21:25 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :  324 (13015 expanded)
%              Number of clauses        :  220 (3441 expanded)
%              Number of leaves         :   27 (4220 expanded)
%              Depth                    :   36
%              Number of atoms          : 1624 (127094 expanded)
%              Number of equality atoms :  636 (28087 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4
          | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK5,X3,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4
              | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK4,X2,X1)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4
                  | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X5,sK3,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4
                      | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1)))
                & v1_funct_2(X4,sK2,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                        & v1_funct_2(X5,X3,sK1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                    & v1_funct_2(X4,X2,sK1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
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
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f48,f61,f60,f59,f58,f57,f56])).

fof(f99,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f106,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f104,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f103,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f101,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f62])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f114,plain,(
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
    inference(equality_resolution,[],[f89])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f96,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f102,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f62])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f55])).

fof(f115,plain,(
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
    inference(equality_resolution,[],[f88])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1436,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_2437,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1436])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2414,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1462])).

cnf(c_3215,plain,
    ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
    inference(superposition,[status(thm)],[c_2437,c_2414])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1442,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2431,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1442])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1448,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2426,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_4321,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_2426])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2969,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3282,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_4915,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4321,c_33,c_31,c_3282])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1439,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2434,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1439])).

cnf(c_4322,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2426])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2974,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3287,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(instantiation,[status(thm)],[c_2974])).

cnf(c_4921,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4322,c_36,c_34,c_3287])).

cnf(c_25,plain,
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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_29,plain,
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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_28,plain,
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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_27,plain,
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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_241,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_29,c_28,c_27])).

cnf(c_242,plain,
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
    inference(renaming,[status(thm)],[c_241])).

cnf(c_1429,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
    | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_2444,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
    | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
    | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
    | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_xboole_0(X3_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2415,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
    | v1_xboole_0(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_2689,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
    | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X4_57) = X5_57
    | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
    | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2444,c_2415])).

cnf(c_12086,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4921,c_2689])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_45,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_46,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_35064,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12086,c_45,c_46,c_51,c_52,c_53])).

cnf(c_35065,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_35064])).

cnf(c_35078,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4915,c_35065])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_48,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_36298,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35078,c_48,c_54,c_55,c_56])).

cnf(c_36308,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3215,c_36298])).

cnf(c_16,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_37,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_611,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_612,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_614,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_41,c_39])).

cnf(c_1428,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_614])).

cnf(c_2445,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1428])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1463,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2413,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1463])).

cnf(c_3807,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2445,c_2413])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1449,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2425,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_4219,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_2425])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_22,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_566,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_18,c_22])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_566,c_22,c_18,c_17])).

cnf(c_571,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_570])).

cnf(c_624,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_19,c_571])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_624,c_22,c_19,c_18,c_17])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_628])).

cnf(c_1427,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | v1_xboole_0(X2_57)
    | k1_relat_1(X0_57) = X1_57 ),
    inference(subtyping,[status(esa)],[c_629])).

cnf(c_2446,plain,
    ( k1_relat_1(X0_57) = X1_57
    | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_5318,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_2446])).

cnf(c_2959,plain,
    ( ~ v1_funct_2(sK5,X0_57,X1_57)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK5) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_3276,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2959])).

cnf(c_5855,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5318,c_42,c_33,c_32,c_31,c_3276])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1455,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2421,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1455])).

cnf(c_5868,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5855,c_2421])).

cnf(c_2843,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_2844,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2843])).

cnf(c_6494,plain,
    ( r1_xboole_0(X0_57,sK3) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5868,c_56,c_2844])).

cnf(c_6495,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6494])).

cnf(c_6502,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2445,c_6495])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1452,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57)
    | ~ v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2422,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1452])).

cnf(c_7274,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6502,c_2422])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1453,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_7282,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7274,c_1453])).

cnf(c_7823,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7282,c_56,c_2844])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1456,plain,
    ( ~ r1_tarski(X0_57,X1_57)
    | ~ v1_relat_1(X2_57)
    | k9_relat_1(k7_relat_1(X2_57,X1_57),X0_57) = k9_relat_1(X2_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2420,plain,
    ( k9_relat_1(k7_relat_1(X0_57,X1_57),X2_57) = k9_relat_1(X0_57,X2_57)
    | r1_tarski(X2_57,X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_7828,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_7823,c_2420])).

cnf(c_8387,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4219,c_7828])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1460,plain,
    ( ~ v1_relat_1(X0_57)
    | v1_relat_1(k7_relat_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2416,plain,
    ( v1_relat_1(X0_57) != iProver_top
    | v1_relat_1(k7_relat_1(X0_57,X1_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1460])).

cnf(c_7275,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6502,c_2416])).

cnf(c_7731,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7275,c_56,c_2844])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1459,plain,
    ( ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2417,plain,
    ( k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1459])).

cnf(c_7736,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7731,c_2417])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1454,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_7737,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7736,c_1453,c_1454])).

cnf(c_8396,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8387,c_6502,c_7737])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1457,plain,
    ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2419,plain,
    ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1457])).

cnf(c_8647,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8396,c_2419])).

cnf(c_8648,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8647,c_5855])).

cnf(c_8651,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8648,c_56,c_2844])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1451,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2423,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_5867,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5855,c_2423])).

cnf(c_6485,plain,
    ( r1_xboole_0(sK3,X0_57) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5867,c_56,c_2844])).

cnf(c_6486,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_6485])).

cnf(c_8659,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8651,c_6486])).

cnf(c_36309,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36308,c_3807,c_8659])).

cnf(c_1446,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2428,plain,
    ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57))) = iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(X3_57) != iProver_top
    | v1_xboole_0(X5_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1446])).

cnf(c_2634,plain,
    ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57))) = iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(X3_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2428,c_2415])).

cnf(c_9009,plain,
    ( k2_partfun1(k4_subset_1(X0_57,X1_57,X2_57),X3_57,k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57) = k7_relat_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57)
    | v1_funct_2(X5_57,X2_57,X3_57) != iProver_top
    | v1_funct_2(X4_57,X1_57,X3_57) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X2_57,X3_57))) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_funct_1(X4_57) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57)) != iProver_top
    | v1_xboole_0(X3_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_2426])).

cnf(c_1444,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57))
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_2430,plain,
    ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(X3_57) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57)) = iProver_top
    | v1_xboole_0(X5_57) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_2582,plain,
    ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_funct_1(X3_57) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57)) = iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2430,c_2415])).

cnf(c_18843,plain,
    ( k2_partfun1(k4_subset_1(X0_57,X1_57,X2_57),X3_57,k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57) = k7_relat_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57)
    | v1_funct_2(X5_57,X2_57,X3_57) != iProver_top
    | v1_funct_2(X4_57,X1_57,X3_57) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X2_57,X3_57))) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_funct_1(X4_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X3_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9009,c_2582])).

cnf(c_18847,plain,
    ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
    | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2431,c_18843])).

cnf(c_19648,plain,
    ( v1_funct_1(X2_57) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
    | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18847,c_45,c_48,c_54,c_55])).

cnf(c_19649,plain,
    ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
    | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_19648])).

cnf(c_19662,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_19649])).

cnf(c_20009,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19662,c_46,c_51,c_52])).

cnf(c_20018,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_20009])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3011,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(sK4,X3_57,X2_57)
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | v1_funct_1(k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK4,X0_57))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X3_57) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_3347,plain,
    ( ~ v1_funct_2(sK5,X0_57,X1_57)
    | ~ v1_funct_2(sK4,X2_57,X1_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
    | v1_funct_1(k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X3_57)
    | v1_xboole_0(X0_57) ),
    inference(instantiation,[status(thm)],[c_3011])).

cnf(c_3794,plain,
    ( ~ v1_funct_2(sK5,X0_57,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_57))
    | v1_funct_1(k1_tmap_1(X1_57,sK1,sK2,X0_57,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3347])).

cnf(c_4173,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_57))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_57))
    | v1_funct_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3794])).

cnf(c_5589,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_3031,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(sK4,X3_57,X2_57)
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | m1_subset_1(k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK4,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4_57,X3_57,X1_57),X2_57)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X3_57) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_3387,plain,
    ( ~ v1_funct_2(sK5,X0_57,X1_57)
    | ~ v1_funct_2(sK4,X2_57,X1_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
    | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
    | m1_subset_1(k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3_57,X2_57,X0_57),X1_57)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X3_57)
    | v1_xboole_0(X0_57) ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_3918,plain,
    ( ~ v1_funct_2(sK5,X0_57,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | m1_subset_1(k1_tmap_1(X1_57,sK1,sK2,X0_57,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1_57,sK2,X0_57),sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_57))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3387])).

cnf(c_4274,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | m1_subset_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0_57,sK2,sK3),sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_57))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_57))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0_57)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3918])).

cnf(c_7003,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_4274])).

cnf(c_6717,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(X0_57,X1_57,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_12798,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
    inference(instantiation,[status(thm)],[c_6717])).

cnf(c_20087,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20018,c_43,c_42,c_41,c_40,c_39,c_38,c_36,c_35,c_34,c_33,c_32,c_31,c_5589,c_7003,c_12798])).

cnf(c_36310,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36309,c_3215,c_20087])).

cnf(c_4220,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2425])).

cnf(c_5319,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2434,c_2446])).

cnf(c_2964,plain,
    ( ~ v1_funct_2(sK4,X0_57,X1_57)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK4) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_3279,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2964])).

cnf(c_5898,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5319,c_42,c_36,c_35,c_34,c_3279])).

cnf(c_5910,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5898,c_2423])).

cnf(c_2846,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1449])).

cnf(c_2847,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_7067,plain,
    ( r1_xboole_0(sK2,X0_57) != iProver_top
    | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5910,c_53,c_2847])).

cnf(c_7068,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_7067])).

cnf(c_7075,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2445,c_7068])).

cnf(c_7366,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7075,c_2422])).

cnf(c_7374,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7366,c_1453])).

cnf(c_8273,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7374,c_53,c_2847])).

cnf(c_8278,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8273,c_2420])).

cnf(c_9741,plain,
    ( k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4220,c_8278])).

cnf(c_9746,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9741,c_7075,c_7737])).

cnf(c_9899,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9746,c_2419])).

cnf(c_9900,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9899,c_5898])).

cnf(c_9903,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9900,c_53,c_2847])).

cnf(c_9911,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9903,c_7068])).

cnf(c_36311,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36310,c_3807,c_9911])).

cnf(c_36312,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_36311])).

cnf(c_30,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1443,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3428,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_3215,c_1443])).

cnf(c_4001,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3807,c_3428])).

cnf(c_4919,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4915,c_4001])).

cnf(c_5164,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4919,c_4921])).

cnf(c_8837,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8659,c_5164])).

cnf(c_10016,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9911,c_8837])).

cnf(c_27037,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_10016])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_26,plain,
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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_234,plain,
    ( ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_2(X3,X4,X2)
    | ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | v1_xboole_0(X5)
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_29,c_28,c_27])).

cnf(c_235,plain,
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
    inference(renaming,[status(thm)],[c_234])).

cnf(c_1430,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
    | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_2443,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
    | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
    | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
    | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_xboole_0(X3_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1430])).

cnf(c_2661,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
    | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X0_57) = X2_57
    | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
    | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
    | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X5_57) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X4_57) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2443,c_2415])).

cnf(c_10551,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4921,c_2661])).

cnf(c_11937,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10551,c_45,c_46,c_51,c_52,c_53])).

cnf(c_11938,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_11937])).

cnf(c_11951,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4915,c_11938])).

cnf(c_12916,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11951,c_48,c_54,c_55,c_56])).

cnf(c_12926,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3215,c_12916])).

cnf(c_12927,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12926,c_3807,c_8659])).

cnf(c_12928,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12927,c_3215])).

cnf(c_12929,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12928,c_3807,c_9911])).

cnf(c_12930,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12929])).

cnf(c_27038,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27037,c_47,c_49,c_8837,c_9911,c_12930])).

cnf(c_27040,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_27038,c_20087])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36312,c_27040,c_49,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.15  % Command    : iproveropt_run.sh %d %s
% 0.16/0.36  % Computer   : n017.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % WCLimit    : 600
% 0.16/0.36  % DateTime   : Tue Dec  1 14:44:01 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running in FOF mode
% 11.38/1.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/1.95  
% 11.38/1.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.38/1.95  
% 11.38/1.95  ------  iProver source info
% 11.38/1.95  
% 11.38/1.95  git: date: 2020-06-30 10:37:57 +0100
% 11.38/1.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.38/1.95  git: non_committed_changes: false
% 11.38/1.95  git: last_make_outside_of_git: false
% 11.38/1.95  
% 11.38/1.95  ------ 
% 11.38/1.95  ------ Parsing...
% 11.38/1.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.38/1.95  
% 11.38/1.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 11.38/1.95  
% 11.38/1.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.38/1.95  
% 11.38/1.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.38/1.95  ------ Proving...
% 11.38/1.95  ------ Problem Properties 
% 11.38/1.95  
% 11.38/1.95  
% 11.38/1.95  clauses                                 38
% 11.38/1.95  conjectures                             13
% 11.38/1.95  EPR                                     9
% 11.38/1.95  Horn                                    31
% 11.38/1.95  unary                                   15
% 11.38/1.95  binary                                  7
% 11.38/1.95  lits                                    145
% 11.38/1.95  lits eq                                 23
% 11.38/1.95  fd_pure                                 0
% 11.38/1.95  fd_pseudo                               0
% 11.38/1.95  fd_cond                                 0
% 11.38/1.95  fd_pseudo_cond                          1
% 11.38/1.95  AC symbols                              0
% 11.38/1.95  
% 11.38/1.95  ------ Input Options Time Limit: Unbounded
% 11.38/1.95  
% 11.38/1.95  
% 11.38/1.95  ------ 
% 11.38/1.95  Current options:
% 11.38/1.95  ------ 
% 11.38/1.95  
% 11.38/1.95  
% 11.38/1.95  
% 11.38/1.95  
% 11.38/1.95  ------ Proving...
% 11.38/1.95  
% 11.38/1.95  
% 11.38/1.95  % SZS status Theorem for theBenchmark.p
% 11.38/1.95  
% 11.38/1.95  % SZS output start CNFRefutation for theBenchmark.p
% 11.38/1.95  
% 11.38/1.95  fof(f21,conjecture,(
% 11.38/1.95    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f22,negated_conjecture,(
% 11.38/1.95    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.38/1.95    inference(negated_conjecture,[],[f21])).
% 11.38/1.95  
% 11.38/1.95  fof(f47,plain,(
% 11.38/1.95    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f22])).
% 11.38/1.95  
% 11.38/1.95  fof(f48,plain,(
% 11.38/1.95    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.38/1.95    inference(flattening,[],[f47])).
% 11.38/1.95  
% 11.38/1.95  fof(f61,plain,(
% 11.38/1.95    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 11.38/1.95    introduced(choice_axiom,[])).
% 11.38/1.95  
% 11.38/1.95  fof(f60,plain,(
% 11.38/1.95    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 11.38/1.95    introduced(choice_axiom,[])).
% 11.38/1.95  
% 11.38/1.95  fof(f59,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 11.38/1.95    introduced(choice_axiom,[])).
% 11.38/1.95  
% 11.38/1.95  fof(f58,plain,(
% 11.38/1.95    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 11.38/1.95    introduced(choice_axiom,[])).
% 11.38/1.95  
% 11.38/1.95  fof(f57,plain,(
% 11.38/1.95    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 11.38/1.95    introduced(choice_axiom,[])).
% 11.38/1.95  
% 11.38/1.95  fof(f56,plain,(
% 11.38/1.95    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 11.38/1.95    introduced(choice_axiom,[])).
% 11.38/1.95  
% 11.38/1.95  fof(f62,plain,(
% 11.38/1.95    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 11.38/1.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f48,f61,f60,f59,f58,f57,f56])).
% 11.38/1.95  
% 11.38/1.95  fof(f99,plain,(
% 11.38/1.95    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f2,axiom,(
% 11.38/1.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f24,plain,(
% 11.38/1.95    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.38/1.95    inference(ennf_transformation,[],[f2])).
% 11.38/1.95  
% 11.38/1.95  fof(f65,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.38/1.95    inference(cnf_transformation,[],[f24])).
% 11.38/1.95  
% 11.38/1.95  fof(f4,axiom,(
% 11.38/1.95    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f67,plain,(
% 11.38/1.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.38/1.95    inference(cnf_transformation,[],[f4])).
% 11.38/1.95  
% 11.38/1.95  fof(f110,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.38/1.95    inference(definition_unfolding,[],[f65,f67])).
% 11.38/1.95  
% 11.38/1.95  fof(f106,plain,(
% 11.38/1.95    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f18,axiom,(
% 11.38/1.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f41,plain,(
% 11.38/1.95    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.38/1.95    inference(ennf_transformation,[],[f18])).
% 11.38/1.95  
% 11.38/1.95  fof(f42,plain,(
% 11.38/1.95    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.38/1.95    inference(flattening,[],[f41])).
% 11.38/1.95  
% 11.38/1.95  fof(f87,plain,(
% 11.38/1.95    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f42])).
% 11.38/1.95  
% 11.38/1.95  fof(f104,plain,(
% 11.38/1.95    v1_funct_1(sK5)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f103,plain,(
% 11.38/1.95    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f101,plain,(
% 11.38/1.95    v1_funct_1(sK4)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f19,axiom,(
% 11.38/1.95    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f43,plain,(
% 11.38/1.95    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f19])).
% 11.38/1.95  
% 11.38/1.95  fof(f44,plain,(
% 11.38/1.95    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.38/1.95    inference(flattening,[],[f43])).
% 11.38/1.95  
% 11.38/1.95  fof(f54,plain,(
% 11.38/1.95    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.38/1.95    inference(nnf_transformation,[],[f44])).
% 11.38/1.95  
% 11.38/1.95  fof(f55,plain,(
% 11.38/1.95    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.38/1.95    inference(flattening,[],[f54])).
% 11.38/1.95  
% 11.38/1.95  fof(f89,plain,(
% 11.38/1.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f55])).
% 11.38/1.95  
% 11.38/1.95  fof(f114,plain,(
% 11.38/1.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(equality_resolution,[],[f89])).
% 11.38/1.95  
% 11.38/1.95  fof(f20,axiom,(
% 11.38/1.95    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f45,plain,(
% 11.38/1.95    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.38/1.95    inference(ennf_transformation,[],[f20])).
% 11.38/1.95  
% 11.38/1.95  fof(f46,plain,(
% 11.38/1.95    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.38/1.95    inference(flattening,[],[f45])).
% 11.38/1.95  
% 11.38/1.95  fof(f91,plain,(
% 11.38/1.95    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f46])).
% 11.38/1.95  
% 11.38/1.95  fof(f92,plain,(
% 11.38/1.95    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f46])).
% 11.38/1.95  
% 11.38/1.95  fof(f93,plain,(
% 11.38/1.95    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f46])).
% 11.38/1.95  
% 11.38/1.95  fof(f3,axiom,(
% 11.38/1.95    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f25,plain,(
% 11.38/1.95    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f3])).
% 11.38/1.95  
% 11.38/1.95  fof(f66,plain,(
% 11.38/1.95    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f25])).
% 11.38/1.95  
% 11.38/1.95  fof(f95,plain,(
% 11.38/1.95    ~v1_xboole_0(sK1)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f96,plain,(
% 11.38/1.95    ~v1_xboole_0(sK2)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f102,plain,(
% 11.38/1.95    v1_funct_2(sK4,sK2,sK1)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f98,plain,(
% 11.38/1.95    ~v1_xboole_0(sK3)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f105,plain,(
% 11.38/1.95    v1_funct_2(sK5,sK3,sK1)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f13,axiom,(
% 11.38/1.95    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f33,plain,(
% 11.38/1.95    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.38/1.95    inference(ennf_transformation,[],[f13])).
% 11.38/1.95  
% 11.38/1.95  fof(f34,plain,(
% 11.38/1.95    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.38/1.95    inference(flattening,[],[f33])).
% 11.38/1.95  
% 11.38/1.95  fof(f52,plain,(
% 11.38/1.95    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.38/1.95    inference(nnf_transformation,[],[f34])).
% 11.38/1.95  
% 11.38/1.95  fof(f79,plain,(
% 11.38/1.95    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f52])).
% 11.38/1.95  
% 11.38/1.95  fof(f100,plain,(
% 11.38/1.95    r1_subset_1(sK2,sK3)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f1,axiom,(
% 11.38/1.95    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f49,plain,(
% 11.38/1.95    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.38/1.95    inference(nnf_transformation,[],[f1])).
% 11.38/1.95  
% 11.38/1.95  fof(f63,plain,(
% 11.38/1.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f49])).
% 11.38/1.95  
% 11.38/1.95  fof(f109,plain,(
% 11.38/1.95    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 11.38/1.95    inference(definition_unfolding,[],[f63,f67])).
% 11.38/1.95  
% 11.38/1.95  fof(f14,axiom,(
% 11.38/1.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f35,plain,(
% 11.38/1.95    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.38/1.95    inference(ennf_transformation,[],[f14])).
% 11.38/1.95  
% 11.38/1.95  fof(f81,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.38/1.95    inference(cnf_transformation,[],[f35])).
% 11.38/1.95  
% 11.38/1.95  fof(f16,axiom,(
% 11.38/1.95    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f37,plain,(
% 11.38/1.95    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.38/1.95    inference(ennf_transformation,[],[f16])).
% 11.38/1.95  
% 11.38/1.95  fof(f38,plain,(
% 11.38/1.95    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.38/1.95    inference(flattening,[],[f37])).
% 11.38/1.95  
% 11.38/1.95  fof(f84,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f38])).
% 11.38/1.95  
% 11.38/1.95  fof(f15,axiom,(
% 11.38/1.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f23,plain,(
% 11.38/1.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.38/1.95    inference(pure_predicate_removal,[],[f15])).
% 11.38/1.95  
% 11.38/1.95  fof(f36,plain,(
% 11.38/1.95    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.38/1.95    inference(ennf_transformation,[],[f23])).
% 11.38/1.95  
% 11.38/1.95  fof(f82,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.38/1.95    inference(cnf_transformation,[],[f36])).
% 11.38/1.95  
% 11.38/1.95  fof(f17,axiom,(
% 11.38/1.95    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f39,plain,(
% 11.38/1.95    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.38/1.95    inference(ennf_transformation,[],[f17])).
% 11.38/1.95  
% 11.38/1.95  fof(f40,plain,(
% 11.38/1.95    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(flattening,[],[f39])).
% 11.38/1.95  
% 11.38/1.95  fof(f53,plain,(
% 11.38/1.95    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(nnf_transformation,[],[f40])).
% 11.38/1.95  
% 11.38/1.95  fof(f85,plain,(
% 11.38/1.95    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f53])).
% 11.38/1.95  
% 11.38/1.95  fof(f9,axiom,(
% 11.38/1.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f30,plain,(
% 11.38/1.95    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f9])).
% 11.38/1.95  
% 11.38/1.95  fof(f73,plain,(
% 11.38/1.95    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f30])).
% 11.38/1.95  
% 11.38/1.95  fof(f11,axiom,(
% 11.38/1.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f31,plain,(
% 11.38/1.95    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(ennf_transformation,[],[f11])).
% 11.38/1.95  
% 11.38/1.95  fof(f76,plain,(
% 11.38/1.95    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f31])).
% 11.38/1.95  
% 11.38/1.95  fof(f10,axiom,(
% 11.38/1.95    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f74,plain,(
% 11.38/1.95    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 11.38/1.95    inference(cnf_transformation,[],[f10])).
% 11.38/1.95  
% 11.38/1.95  fof(f8,axiom,(
% 11.38/1.95    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f29,plain,(
% 11.38/1.95    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f8])).
% 11.38/1.95  
% 11.38/1.95  fof(f72,plain,(
% 11.38/1.95    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f29])).
% 11.38/1.95  
% 11.38/1.95  fof(f5,axiom,(
% 11.38/1.95    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f26,plain,(
% 11.38/1.95    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f5])).
% 11.38/1.95  
% 11.38/1.95  fof(f68,plain,(
% 11.38/1.95    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f26])).
% 11.38/1.95  
% 11.38/1.95  fof(f6,axiom,(
% 11.38/1.95    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f27,plain,(
% 11.38/1.95    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 11.38/1.95    inference(ennf_transformation,[],[f6])).
% 11.38/1.95  
% 11.38/1.95  fof(f69,plain,(
% 11.38/1.95    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f27])).
% 11.38/1.95  
% 11.38/1.95  fof(f75,plain,(
% 11.38/1.95    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 11.38/1.95    inference(cnf_transformation,[],[f10])).
% 11.38/1.95  
% 11.38/1.95  fof(f7,axiom,(
% 11.38/1.95    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f28,plain,(
% 11.38/1.95    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(ennf_transformation,[],[f7])).
% 11.38/1.95  
% 11.38/1.95  fof(f50,plain,(
% 11.38/1.95    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(nnf_transformation,[],[f28])).
% 11.38/1.95  
% 11.38/1.95  fof(f70,plain,(
% 11.38/1.95    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f50])).
% 11.38/1.95  
% 11.38/1.95  fof(f12,axiom,(
% 11.38/1.95    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.38/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.95  
% 11.38/1.95  fof(f32,plain,(
% 11.38/1.95    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(ennf_transformation,[],[f12])).
% 11.38/1.95  
% 11.38/1.95  fof(f51,plain,(
% 11.38/1.95    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.38/1.95    inference(nnf_transformation,[],[f32])).
% 11.38/1.95  
% 11.38/1.95  fof(f78,plain,(
% 11.38/1.95    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f51])).
% 11.38/1.95  
% 11.38/1.95  fof(f94,plain,(
% 11.38/1.95    ~v1_xboole_0(sK0)),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f97,plain,(
% 11.38/1.95    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f107,plain,(
% 11.38/1.95    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 11.38/1.95    inference(cnf_transformation,[],[f62])).
% 11.38/1.95  
% 11.38/1.95  fof(f88,plain,(
% 11.38/1.95    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(cnf_transformation,[],[f55])).
% 11.38/1.95  
% 11.38/1.95  fof(f115,plain,(
% 11.38/1.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.38/1.95    inference(equality_resolution,[],[f88])).
% 11.38/1.95  
% 11.38/1.95  cnf(c_38,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.38/1.95      inference(cnf_transformation,[],[f99]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1436,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_38]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2437,plain,
% 11.38/1.95      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1436]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.95      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 11.38/1.95      inference(cnf_transformation,[],[f110]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1462,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 11.38/1.95      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_2]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2414,plain,
% 11.38/1.95      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1462]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3215,plain,
% 11.38/1.95      ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2437,c_2414]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_31,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.38/1.95      inference(cnf_transformation,[],[f106]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1442,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_31]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2431,plain,
% 11.38/1.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1442]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_23,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.38/1.95      inference(cnf_transformation,[],[f87]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1448,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_23]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2426,plain,
% 11.38/1.95      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X2_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4321,plain,
% 11.38/1.95      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
% 11.38/1.95      | v1_funct_1(sK5) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2431,c_2426]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_33,negated_conjecture,
% 11.38/1.95      ( v1_funct_1(sK5) ),
% 11.38/1.95      inference(cnf_transformation,[],[f104]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2969,plain,
% 11.38/1.95      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1448]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3282,plain,
% 11.38/1.95      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_2969]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4915,plain,
% 11.38/1.95      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_4321,c_33,c_31,c_3282]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_34,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.38/1.95      inference(cnf_transformation,[],[f103]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1439,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_34]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2434,plain,
% 11.38/1.95      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1439]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4322,plain,
% 11.38/1.95      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
% 11.38/1.95      | v1_funct_1(sK4) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2434,c_2426]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36,negated_conjecture,
% 11.38/1.95      ( v1_funct_1(sK4) ),
% 11.38/1.95      inference(cnf_transformation,[],[f101]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2974,plain,
% 11.38/1.95      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1448]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3287,plain,
% 11.38/1.95      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_2974]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4921,plain,
% 11.38/1.95      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_4322,c_36,c_34,c_3287]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_25,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.95      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.38/1.95      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.95      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | ~ v1_funct_1(X3)
% 11.38/1.95      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.38/1.95      | v1_xboole_0(X5)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | v1_xboole_0(X4)
% 11.38/1.95      | v1_xboole_0(X1)
% 11.38/1.95      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f114]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_29,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.95      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | ~ v1_funct_1(X3)
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.38/1.95      | v1_xboole_0(X5)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | v1_xboole_0(X4)
% 11.38/1.95      | v1_xboole_0(X1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f91]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_28,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.95      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.38/1.95      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | ~ v1_funct_1(X3)
% 11.38/1.95      | v1_xboole_0(X5)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | v1_xboole_0(X4)
% 11.38/1.95      | v1_xboole_0(X1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f92]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_27,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.95      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | ~ v1_funct_1(X3)
% 11.38/1.95      | v1_xboole_0(X5)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | v1_xboole_0(X4)
% 11.38/1.95      | v1_xboole_0(X1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f93]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_241,plain,
% 11.38/1.95      ( ~ v1_funct_1(X3)
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.95      | ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.95      | v1_xboole_0(X5)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | v1_xboole_0(X4)
% 11.38/1.95      | v1_xboole_0(X1)
% 11.38/1.95      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_25,c_29,c_28,c_27]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_242,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.95      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | ~ v1_funct_1(X3)
% 11.38/1.95      | v1_xboole_0(X1)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | v1_xboole_0(X4)
% 11.38/1.95      | v1_xboole_0(X5)
% 11.38/1.95      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_241]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1429,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.95      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 11.38/1.95      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 11.38/1.95      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | ~ v1_funct_1(X3_57)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X4_57)
% 11.38/1.95      | v1_xboole_0(X5_57)
% 11.38/1.95      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_242]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2444,plain,
% 11.38/1.95      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 11.38/1.95      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X2_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X5_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X3_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X4_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.38/1.95      | ~ v1_xboole_0(X1)
% 11.38/1.95      | v1_xboole_0(X0) ),
% 11.38/1.95      inference(cnf_transformation,[],[f66]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1461,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 11.38/1.95      | ~ v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X0_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_3]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2415,plain,
% 11.38/1.95      ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2689,plain,
% 11.38/1.95      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X4_57) = X5_57
% 11.38/1.95      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X5_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X2_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X0_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X4_57) = iProver_top ),
% 11.38/1.95      inference(forward_subsumption_resolution,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_2444,c_2415]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_12086,plain,
% 11.38/1.95      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 11.38/1.95      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 11.38/1.95      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.95      | v1_funct_1(X1_57) != iProver_top
% 11.38/1.95      | v1_funct_1(sK4) != iProver_top
% 11.38/1.95      | v1_xboole_0(X0_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(sK1) = iProver_top
% 11.38/1.95      | v1_xboole_0(sK2) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_4921,c_2689]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_42,negated_conjecture,
% 11.38/1.95      ( ~ v1_xboole_0(sK1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f95]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_45,plain,
% 11.38/1.95      ( v1_xboole_0(sK1) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_41,negated_conjecture,
% 11.38/1.95      ( ~ v1_xboole_0(sK2) ),
% 11.38/1.95      inference(cnf_transformation,[],[f96]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_46,plain,
% 11.38/1.95      ( v1_xboole_0(sK2) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_51,plain,
% 11.38/1.95      ( v1_funct_1(sK4) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_35,negated_conjecture,
% 11.38/1.95      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f102]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_52,plain,
% 11.38/1.95      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_53,plain,
% 11.38/1.95      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_35064,plain,
% 11.38/1.95      ( v1_funct_1(X1_57) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.95      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 11.38/1.95      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 11.38/1.95      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 11.38/1.95      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_12086,c_45,c_46,c_51,c_52,c_53]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_35065,plain,
% 11.38/1.95      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 11.38/1.95      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 11.38/1.95      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.95      | v1_funct_1(X1_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_35064]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_35078,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 11.38/1.95      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.38/1.95      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | v1_funct_1(sK5) != iProver_top
% 11.38/1.95      | v1_xboole_0(sK3) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_4915,c_35065]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_39,negated_conjecture,
% 11.38/1.95      ( ~ v1_xboole_0(sK3) ),
% 11.38/1.95      inference(cnf_transformation,[],[f98]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_48,plain,
% 11.38/1.95      ( v1_xboole_0(sK3) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_54,plain,
% 11.38/1.95      ( v1_funct_1(sK5) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_32,negated_conjecture,
% 11.38/1.95      ( v1_funct_2(sK5,sK3,sK1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f105]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_55,plain,
% 11.38/1.95      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_56,plain,
% 11.38/1.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36298,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_35078,c_48,c_54,c_55,c_56]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36308,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_3215,c_36298]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_16,plain,
% 11.38/1.95      ( ~ r1_subset_1(X0,X1)
% 11.38/1.95      | r1_xboole_0(X0,X1)
% 11.38/1.95      | v1_xboole_0(X0)
% 11.38/1.95      | v1_xboole_0(X1) ),
% 11.38/1.95      inference(cnf_transformation,[],[f79]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_37,negated_conjecture,
% 11.38/1.95      ( r1_subset_1(sK2,sK3) ),
% 11.38/1.95      inference(cnf_transformation,[],[f100]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_611,plain,
% 11.38/1.95      ( r1_xboole_0(X0,X1)
% 11.38/1.95      | v1_xboole_0(X0)
% 11.38/1.95      | v1_xboole_0(X1)
% 11.38/1.95      | sK3 != X1
% 11.38/1.95      | sK2 != X0 ),
% 11.38/1.95      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_612,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 11.38/1.95      inference(unflattening,[status(thm)],[c_611]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_614,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,sK3) ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_612,c_41,c_39]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1428,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,sK3) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_614]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2445,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1428]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1,plain,
% 11.38/1.95      ( ~ r1_xboole_0(X0,X1)
% 11.38/1.95      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f109]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1463,plain,
% 11.38/1.95      ( ~ r1_xboole_0(X0_57,X1_57)
% 11.38/1.95      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_1]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2413,plain,
% 11.38/1.95      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1463]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3807,plain,
% 11.38/1.95      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2445,c_2413]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_17,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | v1_relat_1(X0) ),
% 11.38/1.95      inference(cnf_transformation,[],[f81]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1449,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | v1_relat_1(X0_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_17]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2425,plain,
% 11.38/1.95      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 11.38/1.95      | v1_relat_1(X0_57) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4219,plain,
% 11.38/1.95      ( v1_relat_1(sK5) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2431,c_2425]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_19,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | v1_partfun1(X0,X1)
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | v1_xboole_0(X2) ),
% 11.38/1.95      inference(cnf_transformation,[],[f84]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_18,plain,
% 11.38/1.95      ( v4_relat_1(X0,X1)
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.38/1.95      inference(cnf_transformation,[],[f82]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_22,plain,
% 11.38/1.95      ( ~ v1_partfun1(X0,X1)
% 11.38/1.95      | ~ v4_relat_1(X0,X1)
% 11.38/1.95      | ~ v1_relat_1(X0)
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(cnf_transformation,[],[f85]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_566,plain,
% 11.38/1.95      ( ~ v1_partfun1(X0,X1)
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ v1_relat_1(X0)
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(resolution,[status(thm)],[c_18,c_22]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_570,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ v1_partfun1(X0,X1)
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_566,c_22,c_18,c_17]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_571,plain,
% 11.38/1.95      ( ~ v1_partfun1(X0,X1)
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_570]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_624,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(resolution,[status(thm)],[c_19,c_571]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_628,plain,
% 11.38/1.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_624,c_22,c_19,c_18,c_17]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_629,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.95      | ~ v1_funct_1(X0)
% 11.38/1.95      | v1_xboole_0(X2)
% 11.38/1.95      | k1_relat_1(X0) = X1 ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_628]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1427,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | k1_relat_1(X0_57) = X1_57 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_629]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2446,plain,
% 11.38/1.95      ( k1_relat_1(X0_57) = X1_57
% 11.38/1.95      | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X0_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5318,plain,
% 11.38/1.95      ( k1_relat_1(sK5) = sK3
% 11.38/1.95      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.38/1.95      | v1_funct_1(sK5) != iProver_top
% 11.38/1.95      | v1_xboole_0(sK1) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2431,c_2446]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2959,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | k1_relat_1(sK5) = X0_57 ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1427]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3276,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | k1_relat_1(sK5) = sK3 ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_2959]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5855,plain,
% 11.38/1.95      ( k1_relat_1(sK5) = sK3 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_5318,c_42,c_33,c_32,c_31,c_3276]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9,plain,
% 11.38/1.95      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 11.38/1.95      | ~ v1_relat_1(X1)
% 11.38/1.95      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f73]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1455,plain,
% 11.38/1.95      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 11.38/1.95      | ~ v1_relat_1(X1_57)
% 11.38/1.95      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_9]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2421,plain,
% 11.38/1.95      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1455]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5868,plain,
% 11.38/1.95      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(X0_57,sK3) != iProver_top
% 11.38/1.95      | v1_relat_1(sK5) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_5855,c_2421]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2843,plain,
% 11.38/1.95      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | v1_relat_1(sK5) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1449]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2844,plain,
% 11.38/1.95      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.38/1.95      | v1_relat_1(sK5) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_2843]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_6494,plain,
% 11.38/1.95      ( r1_xboole_0(X0_57,sK3) != iProver_top
% 11.38/1.95      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_5868,c_56,c_2844]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_6495,plain,
% 11.38/1.95      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(X0_57,sK3) != iProver_top ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_6494]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_6502,plain,
% 11.38/1.95      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2445,c_6495]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_12,plain,
% 11.38/1.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 11.38/1.95      inference(cnf_transformation,[],[f76]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1452,plain,
% 11.38/1.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57)
% 11.38/1.95      | ~ v1_relat_1(X0_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_12]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2422,plain,
% 11.38/1.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57) = iProver_top
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1452]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7274,plain,
% 11.38/1.95      ( r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
% 11.38/1.95      | v1_relat_1(sK5) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_6502,c_2422]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_11,plain,
% 11.38/1.95      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f74]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1453,plain,
% 11.38/1.95      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_11]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7282,plain,
% 11.38/1.95      ( r1_tarski(k1_xboole_0,sK2) = iProver_top
% 11.38/1.95      | v1_relat_1(sK5) != iProver_top ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_7274,c_1453]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7823,plain,
% 11.38/1.95      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_7282,c_56,c_2844]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8,plain,
% 11.38/1.95      ( ~ r1_tarski(X0,X1)
% 11.38/1.95      | ~ v1_relat_1(X2)
% 11.38/1.95      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 11.38/1.95      inference(cnf_transformation,[],[f72]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1456,plain,
% 11.38/1.95      ( ~ r1_tarski(X0_57,X1_57)
% 11.38/1.95      | ~ v1_relat_1(X2_57)
% 11.38/1.95      | k9_relat_1(k7_relat_1(X2_57,X1_57),X0_57) = k9_relat_1(X2_57,X0_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_8]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2420,plain,
% 11.38/1.95      ( k9_relat_1(k7_relat_1(X0_57,X1_57),X2_57) = k9_relat_1(X0_57,X2_57)
% 11.38/1.95      | r1_tarski(X2_57,X1_57) != iProver_top
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7828,plain,
% 11.38/1.95      ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_7823,c_2420]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8387,plain,
% 11.38/1.95      ( k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_4219,c_7828]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4,plain,
% 11.38/1.95      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 11.38/1.95      inference(cnf_transformation,[],[f68]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1460,plain,
% 11.38/1.95      ( ~ v1_relat_1(X0_57) | v1_relat_1(k7_relat_1(X0_57,X1_57)) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_4]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2416,plain,
% 11.38/1.95      ( v1_relat_1(X0_57) != iProver_top
% 11.38/1.95      | v1_relat_1(k7_relat_1(X0_57,X1_57)) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1460]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7275,plain,
% 11.38/1.95      ( v1_relat_1(sK5) != iProver_top
% 11.38/1.95      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_6502,c_2416]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7731,plain,
% 11.38/1.95      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_7275,c_56,c_2844]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5,plain,
% 11.38/1.95      ( ~ v1_relat_1(X0)
% 11.38/1.95      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 11.38/1.95      inference(cnf_transformation,[],[f69]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1459,plain,
% 11.38/1.95      ( ~ v1_relat_1(X0_57)
% 11.38/1.95      | k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_5]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2417,plain,
% 11.38/1.95      ( k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57)
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1459]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7736,plain,
% 11.38/1.95      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_7731,c_2417]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_10,plain,
% 11.38/1.95      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f75]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1454,plain,
% 11.38/1.95      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_10]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7737,plain,
% 11.38/1.95      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_7736,c_1453,c_1454]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8396,plain,
% 11.38/1.95      ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_8387,c_6502,c_7737]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7,plain,
% 11.38/1.95      ( r1_xboole_0(k1_relat_1(X0),X1)
% 11.38/1.95      | ~ v1_relat_1(X0)
% 11.38/1.95      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f70]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1457,plain,
% 11.38/1.95      ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 11.38/1.95      | ~ v1_relat_1(X0_57)
% 11.38/1.95      | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_7]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2419,plain,
% 11.38/1.95      ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
% 11.38/1.95      | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1457]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8647,plain,
% 11.38/1.95      ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
% 11.38/1.95      | v1_relat_1(sK5) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_8396,c_2419]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8648,plain,
% 11.38/1.95      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
% 11.38/1.95      | v1_relat_1(sK5) != iProver_top ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_8647,c_5855]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8651,plain,
% 11.38/1.95      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_8648,c_56,c_2844]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_13,plain,
% 11.38/1.95      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.38/1.95      | ~ v1_relat_1(X0)
% 11.38/1.95      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 11.38/1.95      inference(cnf_transformation,[],[f78]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1451,plain,
% 11.38/1.95      ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 11.38/1.95      | ~ v1_relat_1(X0_57)
% 11.38/1.95      | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_13]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2423,plain,
% 11.38/1.95      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5867,plain,
% 11.38/1.95      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(sK3,X0_57) != iProver_top
% 11.38/1.95      | v1_relat_1(sK5) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_5855,c_2423]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_6485,plain,
% 11.38/1.95      ( r1_xboole_0(sK3,X0_57) != iProver_top
% 11.38/1.95      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_5867,c_56,c_2844]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_6486,plain,
% 11.38/1.95      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(sK3,X0_57) != iProver_top ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_6485]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8659,plain,
% 11.38/1.95      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_8651,c_6486]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36309,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.95      inference(light_normalisation,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_36308,c_3807,c_8659]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1446,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.95      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 11.38/1.95      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 11.38/1.95      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | ~ v1_funct_1(X3_57)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X4_57)
% 11.38/1.95      | v1_xboole_0(X5_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_27]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2428,plain,
% 11.38/1.95      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57))) = iProver_top
% 11.38/1.95      | v1_funct_1(X0_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X3_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X5_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X4_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1446]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2634,plain,
% 11.38/1.95      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57))) = iProver_top
% 11.38/1.95      | v1_funct_1(X0_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X3_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X4_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top ),
% 11.38/1.95      inference(forward_subsumption_resolution,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_2428,c_2415]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9009,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,X1_57,X2_57),X3_57,k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57) = k7_relat_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57)
% 11.38/1.95      | v1_funct_2(X5_57,X2_57,X3_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X4_57,X1_57,X3_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X2_57,X3_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X5_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X4_57) != iProver_top
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57)) != iProver_top
% 11.38/1.95      | v1_xboole_0(X3_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2634,c_2426]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1444,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.95      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 11.38/1.95      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 11.38/1.95      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | ~ v1_funct_1(X3_57)
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57))
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X4_57)
% 11.38/1.95      | v1_xboole_0(X5_57) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_29]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2430,plain,
% 11.38/1.95      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X0_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X3_57) != iProver_top
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57)) = iProver_top
% 11.38/1.95      | v1_xboole_0(X5_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X4_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2582,plain,
% 11.38/1.95      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X0_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X3_57) != iProver_top
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57)) = iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X4_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top ),
% 11.38/1.95      inference(forward_subsumption_resolution,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_2430,c_2415]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_18843,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,X1_57,X2_57),X3_57,k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57) = k7_relat_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57)
% 11.38/1.95      | v1_funct_2(X5_57,X2_57,X3_57) != iProver_top
% 11.38/1.95      | v1_funct_2(X4_57,X1_57,X3_57) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X2_57,X3_57))) != iProver_top
% 11.38/1.95      | m1_subset_1(X4_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
% 11.38/1.95      | v1_funct_1(X5_57) != iProver_top
% 11.38/1.95      | v1_funct_1(X4_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X2_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(X3_57) = iProver_top ),
% 11.38/1.95      inference(forward_subsumption_resolution,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_9009,c_2582]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_18847,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
% 11.38/1.95      | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
% 11.38/1.95      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | v1_funct_1(X2_57) != iProver_top
% 11.38/1.95      | v1_funct_1(sK5) != iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.95      | v1_xboole_0(sK1) = iProver_top
% 11.38/1.95      | v1_xboole_0(sK3) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2431,c_18843]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_19648,plain,
% 11.38/1.95      ( v1_funct_1(X2_57) != iProver_top
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
% 11.38/1.95      | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_18847,c_45,c_48,c_54,c_55]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_19649,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
% 11.38/1.95      | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
% 11.38/1.95      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | v1_funct_1(X2_57) != iProver_top
% 11.38/1.95      | v1_xboole_0(X1_57) = iProver_top ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_19648]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_19662,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
% 11.38/1.95      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | v1_funct_1(sK4) != iProver_top
% 11.38/1.95      | v1_xboole_0(sK2) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2434,c_19649]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_20009,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_19662,c_46,c_51,c_52]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_20018,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57)
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2437,c_20009]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_43,negated_conjecture,
% 11.38/1.95      ( ~ v1_xboole_0(sK0) ),
% 11.38/1.95      inference(cnf_transformation,[],[f94]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_40,negated_conjecture,
% 11.38/1.95      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 11.38/1.95      inference(cnf_transformation,[],[f97]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3011,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.95      | ~ v1_funct_2(sK4,X3_57,X2_57)
% 11.38/1.95      | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
% 11.38/1.95      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK4,X0_57))
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X4_57)
% 11.38/1.95      | v1_xboole_0(X3_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1444]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3347,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 11.38/1.95      | ~ v1_funct_2(sK4,X2_57,X1_57)
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
% 11.38/1.95      | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK4,sK5))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X3_57)
% 11.38/1.95      | v1_xboole_0(X0_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_3011]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3794,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,X0_57,sK1)
% 11.38/1.95      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_57))
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X1_57,sK1,sK2,X0_57,sK4,sK5))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X0_57)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | v1_xboole_0(sK2) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_3347]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4173,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.38/1.95      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_57))
% 11.38/1.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_57))
% 11.38/1.95      | v1_funct_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X0_57)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | v1_xboole_0(sK3)
% 11.38/1.95      | v1_xboole_0(sK2) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_3794]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5589,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.38/1.95      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.38/1.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.38/1.95      | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | v1_xboole_0(sK3)
% 11.38/1.95      | v1_xboole_0(sK2)
% 11.38/1.95      | v1_xboole_0(sK0) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_4173]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3031,plain,
% 11.38/1.95      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.95      | ~ v1_funct_2(sK4,X3_57,X2_57)
% 11.38/1.95      | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
% 11.38/1.95      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK4,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4_57,X3_57,X1_57),X2_57)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
% 11.38/1.95      | ~ v1_funct_1(X0_57)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X4_57)
% 11.38/1.95      | v1_xboole_0(X3_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1446]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3387,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 11.38/1.95      | ~ v1_funct_2(sK4,X2_57,X1_57)
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
% 11.38/1.95      | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3_57,X2_57,X0_57),X1_57)))
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X2_57)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X3_57)
% 11.38/1.95      | v1_xboole_0(X0_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_3031]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3918,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,X0_57,sK1)
% 11.38/1.95      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X1_57,sK1,sK2,X0_57,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1_57,sK2,X0_57),sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_57))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | v1_xboole_0(X0_57)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | v1_xboole_0(sK2) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_3387]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4274,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.38/1.95      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | m1_subset_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0_57,sK2,sK3),sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_57))
% 11.38/1.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_57))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X0_57)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | v1_xboole_0(sK3)
% 11.38/1.95      | v1_xboole_0(sK2) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_3918]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7003,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.38/1.95      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.38/1.95      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.38/1.95      | ~ v1_funct_1(sK5)
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | v1_xboole_0(sK3)
% 11.38/1.95      | v1_xboole_0(sK2)
% 11.38/1.95      | v1_xboole_0(sK0) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_4274]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_6717,plain,
% 11.38/1.95      ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
% 11.38/1.95      | k2_partfun1(X0_57,X1_57,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1448]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_12798,plain,
% 11.38/1.95      ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
% 11.38/1.95      | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_6717]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_20087,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_20018,c_43,c_42,c_41,c_40,c_39,c_38,c_36,c_35,c_34,
% 11.38/1.95                 c_33,c_32,c_31,c_5589,c_7003,c_12798]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36310,plain,
% 11.38/1.95      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.95      inference(demodulation,[status(thm)],[c_36309,c_3215,c_20087]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4220,plain,
% 11.38/1.95      ( v1_relat_1(sK4) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2434,c_2425]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5319,plain,
% 11.38/1.95      ( k1_relat_1(sK4) = sK2
% 11.38/1.95      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.38/1.95      | v1_funct_1(sK4) != iProver_top
% 11.38/1.95      | v1_xboole_0(sK1) = iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2434,c_2446]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2964,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK4,X0_57,X1_57)
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(X1_57)
% 11.38/1.95      | k1_relat_1(sK4) = X0_57 ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1427]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3279,plain,
% 11.38/1.95      ( ~ v1_funct_2(sK4,sK2,sK1)
% 11.38/1.95      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | ~ v1_funct_1(sK4)
% 11.38/1.95      | v1_xboole_0(sK1)
% 11.38/1.95      | k1_relat_1(sK4) = sK2 ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_2964]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5898,plain,
% 11.38/1.95      ( k1_relat_1(sK4) = sK2 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_5319,c_42,c_36,c_35,c_34,c_3279]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5910,plain,
% 11.38/1.95      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(sK2,X0_57) != iProver_top
% 11.38/1.95      | v1_relat_1(sK4) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_5898,c_2423]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2846,plain,
% 11.38/1.95      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.38/1.95      | v1_relat_1(sK4) ),
% 11.38/1.95      inference(instantiation,[status(thm)],[c_1449]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_2847,plain,
% 11.38/1.95      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.38/1.95      | v1_relat_1(sK4) = iProver_top ),
% 11.38/1.95      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7067,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,X0_57) != iProver_top
% 11.38/1.95      | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_5910,c_53,c_2847]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7068,plain,
% 11.38/1.95      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 11.38/1.95      | r1_xboole_0(sK2,X0_57) != iProver_top ),
% 11.38/1.95      inference(renaming,[status(thm)],[c_7067]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7075,plain,
% 11.38/1.95      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_2445,c_7068]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7366,plain,
% 11.38/1.95      ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
% 11.38/1.95      | v1_relat_1(sK4) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_7075,c_2422]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_7374,plain,
% 11.38/1.95      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 11.38/1.95      | v1_relat_1(sK4) != iProver_top ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_7366,c_1453]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8273,plain,
% 11.38/1.95      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_7374,c_53,c_2847]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_8278,plain,
% 11.38/1.95      ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
% 11.38/1.95      | v1_relat_1(X0_57) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_8273,c_2420]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9741,plain,
% 11.38/1.95      ( k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_4220,c_8278]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9746,plain,
% 11.38/1.95      ( k9_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_9741,c_7075,c_7737]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9899,plain,
% 11.38/1.95      ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top
% 11.38/1.95      | v1_relat_1(sK4) != iProver_top ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_9746,c_2419]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9900,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top
% 11.38/1.95      | v1_relat_1(sK4) != iProver_top ),
% 11.38/1.95      inference(light_normalisation,[status(thm)],[c_9899,c_5898]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9903,plain,
% 11.38/1.95      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
% 11.38/1.95      inference(global_propositional_subsumption,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_9900,c_53,c_2847]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_9911,plain,
% 11.38/1.95      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 11.38/1.95      inference(superposition,[status(thm)],[c_9903,c_7068]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36311,plain,
% 11.38/1.95      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | k1_xboole_0 != k1_xboole_0
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.95      inference(light_normalisation,
% 11.38/1.95                [status(thm)],
% 11.38/1.95                [c_36310,c_3807,c_9911]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_36312,plain,
% 11.38/1.95      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.38/1.95      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.95      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.95      inference(equality_resolution_simp,[status(thm)],[c_36311]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_30,negated_conjecture,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.95      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.38/1.95      inference(cnf_transformation,[],[f107]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_1443,negated_conjecture,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.95      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.38/1.95      inference(subtyping,[status(esa)],[c_30]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_3428,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.95      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 11.38/1.95      inference(demodulation,[status(thm)],[c_3215,c_1443]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4001,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.95      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 11.38/1.95      inference(demodulation,[status(thm)],[c_3807,c_3428]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_4919,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.95      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.38/1.95      inference(demodulation,[status(thm)],[c_4915,c_4001]) ).
% 11.38/1.95  
% 11.38/1.95  cnf(c_5164,plain,
% 11.38/1.95      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.95      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.96      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.38/1.96      inference(demodulation,[status(thm)],[c_4919,c_4921]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_8837,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.96      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.96      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 11.38/1.96      inference(demodulation,[status(thm)],[c_8659,c_5164]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_10016,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.96      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.38/1.96      | k1_xboole_0 != k1_xboole_0 ),
% 11.38/1.96      inference(demodulation,[status(thm)],[c_9911,c_8837]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_27037,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.38/1.96      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 11.38/1.96      inference(equality_resolution_simp,[status(thm)],[c_10016]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_47,plain,
% 11.38/1.96      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.38/1.96      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_49,plain,
% 11.38/1.96      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.38/1.96      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_26,plain,
% 11.38/1.96      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.96      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.96      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.38/1.96      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.96      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.96      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.38/1.96      | ~ v1_funct_1(X0)
% 11.38/1.96      | ~ v1_funct_1(X3)
% 11.38/1.96      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.38/1.96      | v1_xboole_0(X5)
% 11.38/1.96      | v1_xboole_0(X2)
% 11.38/1.96      | v1_xboole_0(X4)
% 11.38/1.96      | v1_xboole_0(X1)
% 11.38/1.96      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.38/1.96      inference(cnf_transformation,[],[f115]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_234,plain,
% 11.38/1.96      ( ~ v1_funct_1(X3)
% 11.38/1.96      | ~ v1_funct_1(X0)
% 11.38/1.96      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.96      | ~ v1_funct_2(X0,X1,X2)
% 11.38/1.96      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.96      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.96      | v1_xboole_0(X5)
% 11.38/1.96      | v1_xboole_0(X2)
% 11.38/1.96      | v1_xboole_0(X4)
% 11.38/1.96      | v1_xboole_0(X1)
% 11.38/1.96      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.38/1.96      inference(global_propositional_subsumption,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_26,c_29,c_28,c_27]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_235,plain,
% 11.38/1.96      ( ~ v1_funct_2(X0,X1,X2)
% 11.38/1.96      | ~ v1_funct_2(X3,X4,X2)
% 11.38/1.96      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.38/1.96      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.38/1.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.38/1.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.38/1.96      | ~ v1_funct_1(X0)
% 11.38/1.96      | ~ v1_funct_1(X3)
% 11.38/1.96      | v1_xboole_0(X1)
% 11.38/1.96      | v1_xboole_0(X2)
% 11.38/1.96      | v1_xboole_0(X4)
% 11.38/1.96      | v1_xboole_0(X5)
% 11.38/1.96      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.38/1.96      inference(renaming,[status(thm)],[c_234]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_1430,plain,
% 11.38/1.96      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 11.38/1.96      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 11.38/1.96      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 11.38/1.96      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 11.38/1.96      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 11.38/1.96      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 11.38/1.96      | ~ v1_funct_1(X0_57)
% 11.38/1.96      | ~ v1_funct_1(X3_57)
% 11.38/1.96      | v1_xboole_0(X2_57)
% 11.38/1.96      | v1_xboole_0(X1_57)
% 11.38/1.96      | v1_xboole_0(X4_57)
% 11.38/1.96      | v1_xboole_0(X5_57)
% 11.38/1.96      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 11.38/1.96      inference(subtyping,[status(esa)],[c_235]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_2443,plain,
% 11.38/1.96      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 11.38/1.96      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 11.38/1.96      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 11.38/1.96      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 11.38/1.96      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 11.38/1.96      | v1_funct_1(X2_57) != iProver_top
% 11.38/1.96      | v1_funct_1(X5_57) != iProver_top
% 11.38/1.96      | v1_xboole_0(X3_57) = iProver_top
% 11.38/1.96      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.96      | v1_xboole_0(X4_57) = iProver_top
% 11.38/1.96      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.96      inference(predicate_to_equality,[status(thm)],[c_1430]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_2661,plain,
% 11.38/1.96      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X0_57) = X2_57
% 11.38/1.96      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 11.38/1.96      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 11.38/1.96      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 11.38/1.96      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 11.38/1.96      | v1_funct_1(X5_57) != iProver_top
% 11.38/1.96      | v1_funct_1(X2_57) != iProver_top
% 11.38/1.96      | v1_xboole_0(X0_57) = iProver_top
% 11.38/1.96      | v1_xboole_0(X1_57) = iProver_top
% 11.38/1.96      | v1_xboole_0(X4_57) = iProver_top ),
% 11.38/1.96      inference(forward_subsumption_resolution,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_2443,c_2415]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_10551,plain,
% 11.38/1.96      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 11.38/1.96      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 11.38/1.96      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.38/1.96      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 11.38/1.96      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.96      | v1_funct_1(X1_57) != iProver_top
% 11.38/1.96      | v1_funct_1(sK4) != iProver_top
% 11.38/1.96      | v1_xboole_0(X0_57) = iProver_top
% 11.38/1.96      | v1_xboole_0(sK1) = iProver_top
% 11.38/1.96      | v1_xboole_0(sK2) = iProver_top ),
% 11.38/1.96      inference(superposition,[status(thm)],[c_4921,c_2661]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_11937,plain,
% 11.38/1.96      ( v1_funct_1(X1_57) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.96      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 11.38/1.96      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 11.38/1.96      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 11.38/1.96      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 11.38/1.96      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.96      inference(global_propositional_subsumption,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_10551,c_45,c_46,c_51,c_52,c_53]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_11938,plain,
% 11.38/1.96      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 11.38/1.96      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 11.38/1.96      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 11.38/1.96      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 11.38/1.96      | v1_funct_1(X1_57) != iProver_top
% 11.38/1.96      | v1_xboole_0(X0_57) = iProver_top ),
% 11.38/1.96      inference(renaming,[status(thm)],[c_11937]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_11951,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 11.38/1.96      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.38/1.96      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.96      | v1_funct_1(sK5) != iProver_top
% 11.38/1.96      | v1_xboole_0(sK3) = iProver_top ),
% 11.38/1.96      inference(superposition,[status(thm)],[c_4915,c_11938]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_12916,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 11.38/1.96      inference(global_propositional_subsumption,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_11951,c_48,c_54,c_55,c_56]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_12926,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.96      inference(superposition,[status(thm)],[c_3215,c_12916]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_12927,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.96      inference(light_normalisation,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_12926,c_3807,c_8659]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_12928,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.96      inference(demodulation,[status(thm)],[c_12927,c_3215]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_12929,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | k1_xboole_0 != k1_xboole_0
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.96      inference(light_normalisation,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_12928,c_3807,c_9911]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_12930,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.38/1.96      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.38/1.96      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.38/1.96      inference(equality_resolution_simp,[status(thm)],[c_12929]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_27038,plain,
% 11.38/1.96      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 11.38/1.96      inference(global_propositional_subsumption,
% 11.38/1.96                [status(thm)],
% 11.38/1.96                [c_27037,c_47,c_49,c_8837,c_9911,c_12930]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(c_27040,plain,
% 11.38/1.96      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 11.38/1.96      inference(demodulation,[status(thm)],[c_27038,c_20087]) ).
% 11.38/1.96  
% 11.38/1.96  cnf(contradiction,plain,
% 11.38/1.96      ( $false ),
% 11.38/1.96      inference(minisat,[status(thm)],[c_36312,c_27040,c_49,c_47]) ).
% 11.38/1.96  
% 11.38/1.96  
% 11.38/1.96  % SZS output end CNFRefutation for theBenchmark.p
% 11.38/1.96  
% 11.38/1.96  ------                               Statistics
% 11.38/1.96  
% 11.38/1.96  ------ Selected
% 11.38/1.96  
% 11.38/1.96  total_time:                             1.123
% 11.38/1.96  
%------------------------------------------------------------------------------
