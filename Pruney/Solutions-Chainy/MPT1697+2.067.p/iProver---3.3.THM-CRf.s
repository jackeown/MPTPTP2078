%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:37 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :  210 (2686 expanded)
%              Number of clauses        :  129 ( 624 expanded)
%              Number of leaves         :   20 (1075 expanded)
%              Depth                    :   27
%              Number of atoms          : 1180 (35175 expanded)
%              Number of equality atoms :  523 (8523 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f49,f48,f47,f46,f45,f44])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
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

fof(f15,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(cnf_transformation,[],[f34])).

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
    inference(cnf_transformation,[],[f34])).

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
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f58])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
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

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1678,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1683,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4042,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_1683])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4096,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4042,c_47])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1672,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1690,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2731,plain,
    ( k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(superposition,[status(thm)],[c_1672,c_1690])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1675,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4043,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_1683])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4137,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4043,c_44])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f96])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f72])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_209,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_22,c_21,c_20])).

cnf(c_210,plain,
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
    inference(renaming,[status(thm)],[c_209])).

cnf(c_1665,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
    | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X5,X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_4143,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_1665])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9055,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4143,c_38,c_39,c_44,c_45,c_46])).

cnf(c_9056,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9055])).

cnf(c_9069,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k2_partfun1(sK3,sK1,X0,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_9056])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_272,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_475,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_476,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_478,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_34,c_32])).

cnf(c_533,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_478])).

cnf(c_534,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_9080,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0,k1_xboole_0)
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9069,c_534])).

cnf(c_9081,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0,k1_xboole_0)
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9080,c_2731])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2725,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_1684])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1691,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1688,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4036,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1691,c_1688])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1685,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4751,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4036,c_1685])).

cnf(c_4766,plain,
    ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_2725,c_4751])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_503,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_5])).

cnf(c_504,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1663,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_2898,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2725,c_1663])).

cnf(c_4973,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4766,c_2898])).

cnf(c_9082,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9081,c_534,c_4973])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9133,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
    | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9082,c_37,c_40,c_41,c_42])).

cnf(c_9139,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_9133])).

cnf(c_2724,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_1684])).

cnf(c_4765,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_2724,c_4751])).

cnf(c_2894,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2724,c_1663])).

cnf(c_4972,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4765,c_2894])).

cnf(c_9140,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9139,c_4972])).

cnf(c_9141,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9140])).

cnf(c_1679,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
    | v1_xboole_0(X5) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1681,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_xboole_0(X5) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4410,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
    | v1_funct_2(X5,X2,X3) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1681,c_1683])).

cnf(c_7259,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
    | v1_funct_2(X5,X2,X3) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1679,c_4410])).

cnf(c_7275,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1678,c_7259])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7287,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7275,c_38,c_41,c_47,c_48])).

cnf(c_7288,plain,
    ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
    | v1_funct_2(X2,X1,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7287])).

cnf(c_7295,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_7288])).

cnf(c_7437,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7295,c_39,c_44,c_45])).

cnf(c_7438,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7437])).

cnf(c_7443,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1672,c_7438])).

cnf(c_7448,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7443,c_37,c_40])).

cnf(c_9142,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9141,c_7448])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2931,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2731,c_23])).

cnf(c_2932,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2931,c_534])).

cnf(c_4099,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4096,c_2932])).

cnf(c_4511,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4099,c_4137])).

cnf(c_7451,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7448,c_4511])).

cnf(c_7455,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7451,c_4972,c_4973])).

cnf(c_7456,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_7455])).

cnf(c_7457,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_7456,c_7448])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f97])).

cnf(c_202,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_22,c_21,c_20])).

cnf(c_203,plain,
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
    inference(renaming,[status(thm)],[c_202])).

cnf(c_1666,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
    | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X5,X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_4100,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4096,c_1666])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4513,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4100,c_38,c_41,c_47,c_48,c_49])).

cnf(c_4514,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4513])).

cnf(c_4520,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4137,c_4514])).

cnf(c_4636,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4520,c_39,c_44,c_45,c_46])).

cnf(c_4637,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4636])).

cnf(c_4642,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_4637])).

cnf(c_4643,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4642,c_534])).

cnf(c_4644,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4643,c_2731])).

cnf(c_4645,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4644,c_534])).

cnf(c_4646,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4645])).

cnf(c_4648,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4645,c_36,c_33,c_31,c_4646])).

cnf(c_4649,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_4648])).

cnf(c_7452,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7448,c_4649])).

cnf(c_7453,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7452,c_4972,c_4973])).

cnf(c_7454,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_7453])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9142,c_7457,c_7454,c_49,c_48,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.28/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.28/1.52  
% 7.28/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.28/1.52  
% 7.28/1.52  ------  iProver source info
% 7.28/1.52  
% 7.28/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.28/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.28/1.52  git: non_committed_changes: false
% 7.28/1.52  git: last_make_outside_of_git: false
% 7.28/1.52  
% 7.28/1.52  ------ 
% 7.28/1.52  
% 7.28/1.52  ------ Input Options
% 7.28/1.52  
% 7.28/1.52  --out_options                           all
% 7.28/1.52  --tptp_safe_out                         true
% 7.28/1.52  --problem_path                          ""
% 7.28/1.52  --include_path                          ""
% 7.28/1.52  --clausifier                            res/vclausify_rel
% 7.28/1.52  --clausifier_options                    ""
% 7.28/1.52  --stdin                                 false
% 7.28/1.52  --stats_out                             all
% 7.28/1.52  
% 7.28/1.52  ------ General Options
% 7.28/1.52  
% 7.28/1.52  --fof                                   false
% 7.28/1.52  --time_out_real                         305.
% 7.28/1.52  --time_out_virtual                      -1.
% 7.28/1.52  --symbol_type_check                     false
% 7.28/1.52  --clausify_out                          false
% 7.28/1.52  --sig_cnt_out                           false
% 7.28/1.52  --trig_cnt_out                          false
% 7.28/1.52  --trig_cnt_out_tolerance                1.
% 7.28/1.52  --trig_cnt_out_sk_spl                   false
% 7.28/1.52  --abstr_cl_out                          false
% 7.28/1.52  
% 7.28/1.52  ------ Global Options
% 7.28/1.52  
% 7.28/1.52  --schedule                              default
% 7.28/1.52  --add_important_lit                     false
% 7.28/1.52  --prop_solver_per_cl                    1000
% 7.28/1.52  --min_unsat_core                        false
% 7.28/1.52  --soft_assumptions                      false
% 7.28/1.52  --soft_lemma_size                       3
% 7.28/1.52  --prop_impl_unit_size                   0
% 7.28/1.52  --prop_impl_unit                        []
% 7.28/1.52  --share_sel_clauses                     true
% 7.28/1.52  --reset_solvers                         false
% 7.28/1.52  --bc_imp_inh                            [conj_cone]
% 7.28/1.52  --conj_cone_tolerance                   3.
% 7.28/1.52  --extra_neg_conj                        none
% 7.28/1.52  --large_theory_mode                     true
% 7.28/1.52  --prolific_symb_bound                   200
% 7.28/1.52  --lt_threshold                          2000
% 7.28/1.52  --clause_weak_htbl                      true
% 7.28/1.52  --gc_record_bc_elim                     false
% 7.28/1.52  
% 7.28/1.52  ------ Preprocessing Options
% 7.28/1.52  
% 7.28/1.52  --preprocessing_flag                    true
% 7.28/1.52  --time_out_prep_mult                    0.1
% 7.28/1.52  --splitting_mode                        input
% 7.28/1.52  --splitting_grd                         true
% 7.28/1.52  --splitting_cvd                         false
% 7.28/1.52  --splitting_cvd_svl                     false
% 7.28/1.52  --splitting_nvd                         32
% 7.28/1.52  --sub_typing                            true
% 7.28/1.52  --prep_gs_sim                           true
% 7.28/1.52  --prep_unflatten                        true
% 7.28/1.52  --prep_res_sim                          true
% 7.28/1.52  --prep_upred                            true
% 7.28/1.52  --prep_sem_filter                       exhaustive
% 7.28/1.52  --prep_sem_filter_out                   false
% 7.28/1.52  --pred_elim                             true
% 7.28/1.52  --res_sim_input                         true
% 7.28/1.52  --eq_ax_congr_red                       true
% 7.28/1.52  --pure_diseq_elim                       true
% 7.28/1.52  --brand_transform                       false
% 7.28/1.52  --non_eq_to_eq                          false
% 7.28/1.52  --prep_def_merge                        true
% 7.28/1.52  --prep_def_merge_prop_impl              false
% 7.28/1.52  --prep_def_merge_mbd                    true
% 7.28/1.52  --prep_def_merge_tr_red                 false
% 7.28/1.52  --prep_def_merge_tr_cl                  false
% 7.28/1.52  --smt_preprocessing                     true
% 7.28/1.52  --smt_ac_axioms                         fast
% 7.28/1.52  --preprocessed_out                      false
% 7.28/1.52  --preprocessed_stats                    false
% 7.28/1.52  
% 7.28/1.52  ------ Abstraction refinement Options
% 7.28/1.52  
% 7.28/1.52  --abstr_ref                             []
% 7.28/1.52  --abstr_ref_prep                        false
% 7.28/1.52  --abstr_ref_until_sat                   false
% 7.28/1.52  --abstr_ref_sig_restrict                funpre
% 7.28/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.28/1.52  --abstr_ref_under                       []
% 7.28/1.52  
% 7.28/1.52  ------ SAT Options
% 7.28/1.52  
% 7.28/1.52  --sat_mode                              false
% 7.28/1.52  --sat_fm_restart_options                ""
% 7.28/1.52  --sat_gr_def                            false
% 7.28/1.52  --sat_epr_types                         true
% 7.28/1.52  --sat_non_cyclic_types                  false
% 7.28/1.52  --sat_finite_models                     false
% 7.28/1.52  --sat_fm_lemmas                         false
% 7.28/1.52  --sat_fm_prep                           false
% 7.28/1.52  --sat_fm_uc_incr                        true
% 7.28/1.52  --sat_out_model                         small
% 7.28/1.52  --sat_out_clauses                       false
% 7.28/1.52  
% 7.28/1.52  ------ QBF Options
% 7.28/1.52  
% 7.28/1.52  --qbf_mode                              false
% 7.28/1.52  --qbf_elim_univ                         false
% 7.28/1.52  --qbf_dom_inst                          none
% 7.28/1.52  --qbf_dom_pre_inst                      false
% 7.28/1.52  --qbf_sk_in                             false
% 7.28/1.52  --qbf_pred_elim                         true
% 7.28/1.52  --qbf_split                             512
% 7.28/1.52  
% 7.28/1.52  ------ BMC1 Options
% 7.28/1.52  
% 7.28/1.52  --bmc1_incremental                      false
% 7.28/1.52  --bmc1_axioms                           reachable_all
% 7.28/1.52  --bmc1_min_bound                        0
% 7.28/1.52  --bmc1_max_bound                        -1
% 7.28/1.52  --bmc1_max_bound_default                -1
% 7.28/1.52  --bmc1_symbol_reachability              true
% 7.28/1.52  --bmc1_property_lemmas                  false
% 7.28/1.52  --bmc1_k_induction                      false
% 7.28/1.52  --bmc1_non_equiv_states                 false
% 7.28/1.52  --bmc1_deadlock                         false
% 7.28/1.52  --bmc1_ucm                              false
% 7.28/1.52  --bmc1_add_unsat_core                   none
% 7.28/1.52  --bmc1_unsat_core_children              false
% 7.28/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.28/1.52  --bmc1_out_stat                         full
% 7.28/1.52  --bmc1_ground_init                      false
% 7.28/1.52  --bmc1_pre_inst_next_state              false
% 7.28/1.52  --bmc1_pre_inst_state                   false
% 7.28/1.52  --bmc1_pre_inst_reach_state             false
% 7.28/1.52  --bmc1_out_unsat_core                   false
% 7.28/1.52  --bmc1_aig_witness_out                  false
% 7.28/1.52  --bmc1_verbose                          false
% 7.28/1.52  --bmc1_dump_clauses_tptp                false
% 7.28/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.28/1.52  --bmc1_dump_file                        -
% 7.28/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.28/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.28/1.52  --bmc1_ucm_extend_mode                  1
% 7.28/1.52  --bmc1_ucm_init_mode                    2
% 7.28/1.52  --bmc1_ucm_cone_mode                    none
% 7.28/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.28/1.52  --bmc1_ucm_relax_model                  4
% 7.28/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.28/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.28/1.52  --bmc1_ucm_layered_model                none
% 7.28/1.52  --bmc1_ucm_max_lemma_size               10
% 7.28/1.52  
% 7.28/1.52  ------ AIG Options
% 7.28/1.52  
% 7.28/1.52  --aig_mode                              false
% 7.28/1.52  
% 7.28/1.52  ------ Instantiation Options
% 7.28/1.52  
% 7.28/1.52  --instantiation_flag                    true
% 7.28/1.52  --inst_sos_flag                         true
% 7.28/1.52  --inst_sos_phase                        true
% 7.28/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.28/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.28/1.52  --inst_lit_sel_side                     num_symb
% 7.28/1.52  --inst_solver_per_active                1400
% 7.28/1.52  --inst_solver_calls_frac                1.
% 7.28/1.52  --inst_passive_queue_type               priority_queues
% 7.28/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.28/1.52  --inst_passive_queues_freq              [25;2]
% 7.28/1.52  --inst_dismatching                      true
% 7.28/1.52  --inst_eager_unprocessed_to_passive     true
% 7.28/1.52  --inst_prop_sim_given                   true
% 7.28/1.52  --inst_prop_sim_new                     false
% 7.28/1.52  --inst_subs_new                         false
% 7.28/1.52  --inst_eq_res_simp                      false
% 7.28/1.52  --inst_subs_given                       false
% 7.28/1.52  --inst_orphan_elimination               true
% 7.28/1.52  --inst_learning_loop_flag               true
% 7.28/1.52  --inst_learning_start                   3000
% 7.28/1.52  --inst_learning_factor                  2
% 7.28/1.52  --inst_start_prop_sim_after_learn       3
% 7.28/1.52  --inst_sel_renew                        solver
% 7.28/1.52  --inst_lit_activity_flag                true
% 7.28/1.52  --inst_restr_to_given                   false
% 7.28/1.52  --inst_activity_threshold               500
% 7.28/1.52  --inst_out_proof                        true
% 7.28/1.52  
% 7.28/1.52  ------ Resolution Options
% 7.28/1.52  
% 7.28/1.52  --resolution_flag                       true
% 7.28/1.52  --res_lit_sel                           adaptive
% 7.28/1.52  --res_lit_sel_side                      none
% 7.28/1.52  --res_ordering                          kbo
% 7.28/1.52  --res_to_prop_solver                    active
% 7.28/1.52  --res_prop_simpl_new                    false
% 7.28/1.52  --res_prop_simpl_given                  true
% 7.28/1.52  --res_passive_queue_type                priority_queues
% 7.28/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.28/1.52  --res_passive_queues_freq               [15;5]
% 7.28/1.52  --res_forward_subs                      full
% 7.28/1.52  --res_backward_subs                     full
% 7.28/1.52  --res_forward_subs_resolution           true
% 7.28/1.52  --res_backward_subs_resolution          true
% 7.28/1.52  --res_orphan_elimination                true
% 7.28/1.52  --res_time_limit                        2.
% 7.28/1.52  --res_out_proof                         true
% 7.28/1.52  
% 7.28/1.52  ------ Superposition Options
% 7.28/1.52  
% 7.28/1.52  --superposition_flag                    true
% 7.28/1.52  --sup_passive_queue_type                priority_queues
% 7.28/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.28/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.28/1.52  --demod_completeness_check              fast
% 7.28/1.52  --demod_use_ground                      true
% 7.28/1.52  --sup_to_prop_solver                    passive
% 7.28/1.52  --sup_prop_simpl_new                    true
% 7.28/1.52  --sup_prop_simpl_given                  true
% 7.28/1.52  --sup_fun_splitting                     true
% 7.28/1.52  --sup_smt_interval                      50000
% 7.28/1.52  
% 7.28/1.52  ------ Superposition Simplification Setup
% 7.28/1.52  
% 7.28/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.28/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.28/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.28/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.28/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.28/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.28/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.28/1.52  --sup_immed_triv                        [TrivRules]
% 7.28/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.28/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.28/1.52  --sup_immed_bw_main                     []
% 7.28/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.28/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.28/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.28/1.52  --sup_input_bw                          []
% 7.28/1.52  
% 7.28/1.52  ------ Combination Options
% 7.28/1.52  
% 7.28/1.52  --comb_res_mult                         3
% 7.28/1.52  --comb_sup_mult                         2
% 7.28/1.52  --comb_inst_mult                        10
% 7.28/1.52  
% 7.28/1.52  ------ Debug Options
% 7.28/1.52  
% 7.28/1.52  --dbg_backtrace                         false
% 7.28/1.52  --dbg_dump_prop_clauses                 false
% 7.28/1.52  --dbg_dump_prop_clauses_file            -
% 7.28/1.52  --dbg_out_stat                          false
% 7.28/1.52  ------ Parsing...
% 7.28/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.28/1.52  
% 7.28/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.28/1.52  
% 7.28/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.28/1.52  
% 7.28/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.28/1.52  ------ Proving...
% 7.28/1.52  ------ Problem Properties 
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  clauses                                 34
% 7.28/1.52  conjectures                             13
% 7.28/1.52  EPR                                     10
% 7.28/1.52  Horn                                    28
% 7.28/1.52  unary                                   16
% 7.28/1.52  binary                                  4
% 7.28/1.52  lits                                    133
% 7.28/1.52  lits eq                                 19
% 7.28/1.52  fd_pure                                 0
% 7.28/1.52  fd_pseudo                               0
% 7.28/1.52  fd_cond                                 0
% 7.28/1.52  fd_pseudo_cond                          1
% 7.28/1.52  AC symbols                              0
% 7.28/1.52  
% 7.28/1.52  ------ Schedule dynamic 5 is on 
% 7.28/1.52  
% 7.28/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  ------ 
% 7.28/1.52  Current options:
% 7.28/1.52  ------ 
% 7.28/1.52  
% 7.28/1.52  ------ Input Options
% 7.28/1.52  
% 7.28/1.52  --out_options                           all
% 7.28/1.52  --tptp_safe_out                         true
% 7.28/1.52  --problem_path                          ""
% 7.28/1.52  --include_path                          ""
% 7.28/1.52  --clausifier                            res/vclausify_rel
% 7.28/1.52  --clausifier_options                    ""
% 7.28/1.52  --stdin                                 false
% 7.28/1.52  --stats_out                             all
% 7.28/1.52  
% 7.28/1.52  ------ General Options
% 7.28/1.52  
% 7.28/1.52  --fof                                   false
% 7.28/1.52  --time_out_real                         305.
% 7.28/1.52  --time_out_virtual                      -1.
% 7.28/1.52  --symbol_type_check                     false
% 7.28/1.52  --clausify_out                          false
% 7.28/1.52  --sig_cnt_out                           false
% 7.28/1.52  --trig_cnt_out                          false
% 7.28/1.52  --trig_cnt_out_tolerance                1.
% 7.28/1.52  --trig_cnt_out_sk_spl                   false
% 7.28/1.52  --abstr_cl_out                          false
% 7.28/1.52  
% 7.28/1.52  ------ Global Options
% 7.28/1.52  
% 7.28/1.52  --schedule                              default
% 7.28/1.52  --add_important_lit                     false
% 7.28/1.52  --prop_solver_per_cl                    1000
% 7.28/1.52  --min_unsat_core                        false
% 7.28/1.52  --soft_assumptions                      false
% 7.28/1.52  --soft_lemma_size                       3
% 7.28/1.52  --prop_impl_unit_size                   0
% 7.28/1.52  --prop_impl_unit                        []
% 7.28/1.52  --share_sel_clauses                     true
% 7.28/1.52  --reset_solvers                         false
% 7.28/1.52  --bc_imp_inh                            [conj_cone]
% 7.28/1.52  --conj_cone_tolerance                   3.
% 7.28/1.52  --extra_neg_conj                        none
% 7.28/1.52  --large_theory_mode                     true
% 7.28/1.52  --prolific_symb_bound                   200
% 7.28/1.52  --lt_threshold                          2000
% 7.28/1.52  --clause_weak_htbl                      true
% 7.28/1.52  --gc_record_bc_elim                     false
% 7.28/1.52  
% 7.28/1.52  ------ Preprocessing Options
% 7.28/1.52  
% 7.28/1.52  --preprocessing_flag                    true
% 7.28/1.52  --time_out_prep_mult                    0.1
% 7.28/1.52  --splitting_mode                        input
% 7.28/1.52  --splitting_grd                         true
% 7.28/1.52  --splitting_cvd                         false
% 7.28/1.52  --splitting_cvd_svl                     false
% 7.28/1.52  --splitting_nvd                         32
% 7.28/1.52  --sub_typing                            true
% 7.28/1.52  --prep_gs_sim                           true
% 7.28/1.52  --prep_unflatten                        true
% 7.28/1.52  --prep_res_sim                          true
% 7.28/1.52  --prep_upred                            true
% 7.28/1.52  --prep_sem_filter                       exhaustive
% 7.28/1.52  --prep_sem_filter_out                   false
% 7.28/1.52  --pred_elim                             true
% 7.28/1.52  --res_sim_input                         true
% 7.28/1.52  --eq_ax_congr_red                       true
% 7.28/1.52  --pure_diseq_elim                       true
% 7.28/1.52  --brand_transform                       false
% 7.28/1.52  --non_eq_to_eq                          false
% 7.28/1.52  --prep_def_merge                        true
% 7.28/1.52  --prep_def_merge_prop_impl              false
% 7.28/1.52  --prep_def_merge_mbd                    true
% 7.28/1.52  --prep_def_merge_tr_red                 false
% 7.28/1.52  --prep_def_merge_tr_cl                  false
% 7.28/1.52  --smt_preprocessing                     true
% 7.28/1.52  --smt_ac_axioms                         fast
% 7.28/1.52  --preprocessed_out                      false
% 7.28/1.52  --preprocessed_stats                    false
% 7.28/1.52  
% 7.28/1.52  ------ Abstraction refinement Options
% 7.28/1.52  
% 7.28/1.52  --abstr_ref                             []
% 7.28/1.52  --abstr_ref_prep                        false
% 7.28/1.52  --abstr_ref_until_sat                   false
% 7.28/1.52  --abstr_ref_sig_restrict                funpre
% 7.28/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.28/1.52  --abstr_ref_under                       []
% 7.28/1.52  
% 7.28/1.52  ------ SAT Options
% 7.28/1.52  
% 7.28/1.52  --sat_mode                              false
% 7.28/1.52  --sat_fm_restart_options                ""
% 7.28/1.52  --sat_gr_def                            false
% 7.28/1.52  --sat_epr_types                         true
% 7.28/1.52  --sat_non_cyclic_types                  false
% 7.28/1.52  --sat_finite_models                     false
% 7.28/1.52  --sat_fm_lemmas                         false
% 7.28/1.52  --sat_fm_prep                           false
% 7.28/1.52  --sat_fm_uc_incr                        true
% 7.28/1.52  --sat_out_model                         small
% 7.28/1.52  --sat_out_clauses                       false
% 7.28/1.52  
% 7.28/1.52  ------ QBF Options
% 7.28/1.52  
% 7.28/1.52  --qbf_mode                              false
% 7.28/1.52  --qbf_elim_univ                         false
% 7.28/1.52  --qbf_dom_inst                          none
% 7.28/1.52  --qbf_dom_pre_inst                      false
% 7.28/1.52  --qbf_sk_in                             false
% 7.28/1.52  --qbf_pred_elim                         true
% 7.28/1.52  --qbf_split                             512
% 7.28/1.52  
% 7.28/1.52  ------ BMC1 Options
% 7.28/1.52  
% 7.28/1.52  --bmc1_incremental                      false
% 7.28/1.52  --bmc1_axioms                           reachable_all
% 7.28/1.52  --bmc1_min_bound                        0
% 7.28/1.52  --bmc1_max_bound                        -1
% 7.28/1.52  --bmc1_max_bound_default                -1
% 7.28/1.52  --bmc1_symbol_reachability              true
% 7.28/1.52  --bmc1_property_lemmas                  false
% 7.28/1.52  --bmc1_k_induction                      false
% 7.28/1.52  --bmc1_non_equiv_states                 false
% 7.28/1.52  --bmc1_deadlock                         false
% 7.28/1.52  --bmc1_ucm                              false
% 7.28/1.52  --bmc1_add_unsat_core                   none
% 7.28/1.52  --bmc1_unsat_core_children              false
% 7.28/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.28/1.52  --bmc1_out_stat                         full
% 7.28/1.52  --bmc1_ground_init                      false
% 7.28/1.52  --bmc1_pre_inst_next_state              false
% 7.28/1.52  --bmc1_pre_inst_state                   false
% 7.28/1.52  --bmc1_pre_inst_reach_state             false
% 7.28/1.52  --bmc1_out_unsat_core                   false
% 7.28/1.52  --bmc1_aig_witness_out                  false
% 7.28/1.52  --bmc1_verbose                          false
% 7.28/1.52  --bmc1_dump_clauses_tptp                false
% 7.28/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.28/1.52  --bmc1_dump_file                        -
% 7.28/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.28/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.28/1.52  --bmc1_ucm_extend_mode                  1
% 7.28/1.52  --bmc1_ucm_init_mode                    2
% 7.28/1.52  --bmc1_ucm_cone_mode                    none
% 7.28/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.28/1.52  --bmc1_ucm_relax_model                  4
% 7.28/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.28/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.28/1.52  --bmc1_ucm_layered_model                none
% 7.28/1.52  --bmc1_ucm_max_lemma_size               10
% 7.28/1.52  
% 7.28/1.52  ------ AIG Options
% 7.28/1.52  
% 7.28/1.52  --aig_mode                              false
% 7.28/1.52  
% 7.28/1.52  ------ Instantiation Options
% 7.28/1.52  
% 7.28/1.52  --instantiation_flag                    true
% 7.28/1.52  --inst_sos_flag                         true
% 7.28/1.52  --inst_sos_phase                        true
% 7.28/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.28/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.28/1.52  --inst_lit_sel_side                     none
% 7.28/1.52  --inst_solver_per_active                1400
% 7.28/1.52  --inst_solver_calls_frac                1.
% 7.28/1.52  --inst_passive_queue_type               priority_queues
% 7.28/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.28/1.52  --inst_passive_queues_freq              [25;2]
% 7.28/1.52  --inst_dismatching                      true
% 7.28/1.52  --inst_eager_unprocessed_to_passive     true
% 7.28/1.52  --inst_prop_sim_given                   true
% 7.28/1.52  --inst_prop_sim_new                     false
% 7.28/1.52  --inst_subs_new                         false
% 7.28/1.52  --inst_eq_res_simp                      false
% 7.28/1.52  --inst_subs_given                       false
% 7.28/1.52  --inst_orphan_elimination               true
% 7.28/1.52  --inst_learning_loop_flag               true
% 7.28/1.52  --inst_learning_start                   3000
% 7.28/1.52  --inst_learning_factor                  2
% 7.28/1.52  --inst_start_prop_sim_after_learn       3
% 7.28/1.52  --inst_sel_renew                        solver
% 7.28/1.52  --inst_lit_activity_flag                true
% 7.28/1.52  --inst_restr_to_given                   false
% 7.28/1.52  --inst_activity_threshold               500
% 7.28/1.52  --inst_out_proof                        true
% 7.28/1.52  
% 7.28/1.52  ------ Resolution Options
% 7.28/1.52  
% 7.28/1.52  --resolution_flag                       false
% 7.28/1.52  --res_lit_sel                           adaptive
% 7.28/1.52  --res_lit_sel_side                      none
% 7.28/1.52  --res_ordering                          kbo
% 7.28/1.52  --res_to_prop_solver                    active
% 7.28/1.52  --res_prop_simpl_new                    false
% 7.28/1.52  --res_prop_simpl_given                  true
% 7.28/1.52  --res_passive_queue_type                priority_queues
% 7.28/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.28/1.52  --res_passive_queues_freq               [15;5]
% 7.28/1.52  --res_forward_subs                      full
% 7.28/1.52  --res_backward_subs                     full
% 7.28/1.52  --res_forward_subs_resolution           true
% 7.28/1.52  --res_backward_subs_resolution          true
% 7.28/1.52  --res_orphan_elimination                true
% 7.28/1.52  --res_time_limit                        2.
% 7.28/1.52  --res_out_proof                         true
% 7.28/1.52  
% 7.28/1.52  ------ Superposition Options
% 7.28/1.52  
% 7.28/1.52  --superposition_flag                    true
% 7.28/1.52  --sup_passive_queue_type                priority_queues
% 7.28/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.28/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.28/1.52  --demod_completeness_check              fast
% 7.28/1.52  --demod_use_ground                      true
% 7.28/1.52  --sup_to_prop_solver                    passive
% 7.28/1.52  --sup_prop_simpl_new                    true
% 7.28/1.52  --sup_prop_simpl_given                  true
% 7.28/1.52  --sup_fun_splitting                     true
% 7.28/1.52  --sup_smt_interval                      50000
% 7.28/1.52  
% 7.28/1.52  ------ Superposition Simplification Setup
% 7.28/1.52  
% 7.28/1.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.28/1.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.28/1.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.28/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.28/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.28/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.28/1.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.28/1.52  --sup_immed_triv                        [TrivRules]
% 7.28/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.28/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.28/1.52  --sup_immed_bw_main                     []
% 7.28/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.28/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.28/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.28/1.52  --sup_input_bw                          []
% 7.28/1.52  
% 7.28/1.52  ------ Combination Options
% 7.28/1.52  
% 7.28/1.52  --comb_res_mult                         3
% 7.28/1.52  --comb_sup_mult                         2
% 7.28/1.52  --comb_inst_mult                        10
% 7.28/1.52  
% 7.28/1.52  ------ Debug Options
% 7.28/1.52  
% 7.28/1.52  --dbg_backtrace                         false
% 7.28/1.52  --dbg_dump_prop_clauses                 false
% 7.28/1.52  --dbg_dump_prop_clauses_file            -
% 7.28/1.52  --dbg_out_stat                          false
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  ------ Proving...
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  % SZS status Theorem for theBenchmark.p
% 7.28/1.52  
% 7.28/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.28/1.52  
% 7.28/1.52  fof(f16,conjecture,(
% 7.28/1.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f17,negated_conjecture,(
% 7.28/1.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.28/1.52    inference(negated_conjecture,[],[f16])).
% 7.28/1.52  
% 7.28/1.52  fof(f35,plain,(
% 7.28/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.28/1.52    inference(ennf_transformation,[],[f17])).
% 7.28/1.52  
% 7.28/1.52  fof(f36,plain,(
% 7.28/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.28/1.52    inference(flattening,[],[f35])).
% 7.28/1.52  
% 7.28/1.52  fof(f49,plain,(
% 7.28/1.52    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.28/1.52    introduced(choice_axiom,[])).
% 7.28/1.52  
% 7.28/1.52  fof(f48,plain,(
% 7.28/1.52    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.28/1.52    introduced(choice_axiom,[])).
% 7.28/1.52  
% 7.28/1.52  fof(f47,plain,(
% 7.28/1.52    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.28/1.52    introduced(choice_axiom,[])).
% 7.28/1.52  
% 7.28/1.52  fof(f46,plain,(
% 7.28/1.52    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.28/1.52    introduced(choice_axiom,[])).
% 7.28/1.52  
% 7.28/1.52  fof(f45,plain,(
% 7.28/1.52    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.28/1.52    introduced(choice_axiom,[])).
% 7.28/1.52  
% 7.28/1.52  fof(f44,plain,(
% 7.28/1.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.28/1.52    introduced(choice_axiom,[])).
% 7.28/1.52  
% 7.28/1.52  fof(f50,plain,(
% 7.28/1.52    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.28/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f49,f48,f47,f46,f45,f44])).
% 7.28/1.52  
% 7.28/1.52  fof(f87,plain,(
% 7.28/1.52    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f13,axiom,(
% 7.28/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f29,plain,(
% 7.28/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.28/1.52    inference(ennf_transformation,[],[f13])).
% 7.28/1.52  
% 7.28/1.52  fof(f30,plain,(
% 7.28/1.52    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.28/1.52    inference(flattening,[],[f29])).
% 7.28/1.52  
% 7.28/1.52  fof(f68,plain,(
% 7.28/1.52    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f30])).
% 7.28/1.52  
% 7.28/1.52  fof(f85,plain,(
% 7.28/1.52    v1_funct_1(sK5)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f80,plain,(
% 7.28/1.52    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f4,axiom,(
% 7.28/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f18,plain,(
% 7.28/1.52    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.28/1.52    inference(ennf_transformation,[],[f4])).
% 7.28/1.52  
% 7.28/1.52  fof(f57,plain,(
% 7.28/1.52    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.28/1.52    inference(cnf_transformation,[],[f18])).
% 7.28/1.52  
% 7.28/1.52  fof(f5,axiom,(
% 7.28/1.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f58,plain,(
% 7.28/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.28/1.52    inference(cnf_transformation,[],[f5])).
% 7.28/1.52  
% 7.28/1.52  fof(f91,plain,(
% 7.28/1.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.28/1.52    inference(definition_unfolding,[],[f57,f58])).
% 7.28/1.52  
% 7.28/1.52  fof(f84,plain,(
% 7.28/1.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f82,plain,(
% 7.28/1.52    v1_funct_1(sK4)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f14,axiom,(
% 7.28/1.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f31,plain,(
% 7.28/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.28/1.52    inference(ennf_transformation,[],[f14])).
% 7.28/1.52  
% 7.28/1.52  fof(f32,plain,(
% 7.28/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.28/1.52    inference(flattening,[],[f31])).
% 7.28/1.52  
% 7.28/1.52  fof(f42,plain,(
% 7.28/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.28/1.52    inference(nnf_transformation,[],[f32])).
% 7.28/1.52  
% 7.28/1.52  fof(f43,plain,(
% 7.28/1.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.28/1.52    inference(flattening,[],[f42])).
% 7.28/1.52  
% 7.28/1.52  fof(f70,plain,(
% 7.28/1.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f43])).
% 7.28/1.52  
% 7.28/1.52  fof(f96,plain,(
% 7.28/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(equality_resolution,[],[f70])).
% 7.28/1.52  
% 7.28/1.52  fof(f15,axiom,(
% 7.28/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f33,plain,(
% 7.28/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.28/1.52    inference(ennf_transformation,[],[f15])).
% 7.28/1.52  
% 7.28/1.52  fof(f34,plain,(
% 7.28/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.28/1.52    inference(flattening,[],[f33])).
% 7.28/1.52  
% 7.28/1.52  fof(f72,plain,(
% 7.28/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f34])).
% 7.28/1.52  
% 7.28/1.52  fof(f73,plain,(
% 7.28/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f34])).
% 7.28/1.52  
% 7.28/1.52  fof(f74,plain,(
% 7.28/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f34])).
% 7.28/1.52  
% 7.28/1.52  fof(f76,plain,(
% 7.28/1.52    ~v1_xboole_0(sK1)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f77,plain,(
% 7.28/1.52    ~v1_xboole_0(sK2)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f83,plain,(
% 7.28/1.52    v1_funct_2(sK4,sK2,sK1)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f1,axiom,(
% 7.28/1.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f37,plain,(
% 7.28/1.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.28/1.52    inference(nnf_transformation,[],[f1])).
% 7.28/1.52  
% 7.28/1.52  fof(f51,plain,(
% 7.28/1.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f37])).
% 7.28/1.52  
% 7.28/1.52  fof(f90,plain,(
% 7.28/1.52    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.28/1.52    inference(definition_unfolding,[],[f51,f58])).
% 7.28/1.52  
% 7.28/1.52  fof(f11,axiom,(
% 7.28/1.52    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f26,plain,(
% 7.28/1.52    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.28/1.52    inference(ennf_transformation,[],[f11])).
% 7.28/1.52  
% 7.28/1.52  fof(f27,plain,(
% 7.28/1.52    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.28/1.52    inference(flattening,[],[f26])).
% 7.28/1.52  
% 7.28/1.52  fof(f41,plain,(
% 7.28/1.52    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.28/1.52    inference(nnf_transformation,[],[f27])).
% 7.28/1.52  
% 7.28/1.52  fof(f65,plain,(
% 7.28/1.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f41])).
% 7.28/1.52  
% 7.28/1.52  fof(f81,plain,(
% 7.28/1.52    r1_subset_1(sK2,sK3)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f79,plain,(
% 7.28/1.52    ~v1_xboole_0(sK3)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f12,axiom,(
% 7.28/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f28,plain,(
% 7.28/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.28/1.52    inference(ennf_transformation,[],[f12])).
% 7.28/1.52  
% 7.28/1.52  fof(f67,plain,(
% 7.28/1.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.28/1.52    inference(cnf_transformation,[],[f28])).
% 7.28/1.52  
% 7.28/1.52  fof(f2,axiom,(
% 7.28/1.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f38,plain,(
% 7.28/1.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.28/1.52    inference(nnf_transformation,[],[f2])).
% 7.28/1.52  
% 7.28/1.52  fof(f39,plain,(
% 7.28/1.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.28/1.52    inference(flattening,[],[f38])).
% 7.28/1.52  
% 7.28/1.52  fof(f53,plain,(
% 7.28/1.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.28/1.52    inference(cnf_transformation,[],[f39])).
% 7.28/1.52  
% 7.28/1.52  fof(f93,plain,(
% 7.28/1.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.28/1.52    inference(equality_resolution,[],[f53])).
% 7.28/1.52  
% 7.28/1.52  fof(f7,axiom,(
% 7.28/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f21,plain,(
% 7.28/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.28/1.52    inference(ennf_transformation,[],[f7])).
% 7.28/1.52  
% 7.28/1.52  fof(f40,plain,(
% 7.28/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.28/1.52    inference(nnf_transformation,[],[f21])).
% 7.28/1.52  
% 7.28/1.52  fof(f61,plain,(
% 7.28/1.52    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f40])).
% 7.28/1.52  
% 7.28/1.52  fof(f10,axiom,(
% 7.28/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f24,plain,(
% 7.28/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.28/1.52    inference(ennf_transformation,[],[f10])).
% 7.28/1.52  
% 7.28/1.52  fof(f25,plain,(
% 7.28/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.28/1.52    inference(flattening,[],[f24])).
% 7.28/1.52  
% 7.28/1.52  fof(f64,plain,(
% 7.28/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f25])).
% 7.28/1.52  
% 7.28/1.52  fof(f9,axiom,(
% 7.28/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f22,plain,(
% 7.28/1.52    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.28/1.52    inference(ennf_transformation,[],[f9])).
% 7.28/1.52  
% 7.28/1.52  fof(f23,plain,(
% 7.28/1.52    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.28/1.52    inference(flattening,[],[f22])).
% 7.28/1.52  
% 7.28/1.52  fof(f63,plain,(
% 7.28/1.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f23])).
% 7.28/1.52  
% 7.28/1.52  fof(f3,axiom,(
% 7.28/1.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.28/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.28/1.52  
% 7.28/1.52  fof(f56,plain,(
% 7.28/1.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f3])).
% 7.28/1.52  
% 7.28/1.52  fof(f75,plain,(
% 7.28/1.52    ~v1_xboole_0(sK0)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f78,plain,(
% 7.28/1.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f86,plain,(
% 7.28/1.52    v1_funct_2(sK5,sK3,sK1)),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f88,plain,(
% 7.28/1.52    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.28/1.52    inference(cnf_transformation,[],[f50])).
% 7.28/1.52  
% 7.28/1.52  fof(f69,plain,(
% 7.28/1.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(cnf_transformation,[],[f43])).
% 7.28/1.52  
% 7.28/1.52  fof(f97,plain,(
% 7.28/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.28/1.52    inference(equality_resolution,[],[f69])).
% 7.28/1.52  
% 7.28/1.52  cnf(c_24,negated_conjecture,
% 7.28/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.28/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1678,plain,
% 7.28/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_16,plain,
% 7.28/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.28/1.52      inference(cnf_transformation,[],[f68]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1683,plain,
% 7.28/1.52      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.28/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4042,plain,
% 7.28/1.52      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1678,c_1683]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_26,negated_conjecture,
% 7.28/1.52      ( v1_funct_1(sK5) ),
% 7.28/1.52      inference(cnf_transformation,[],[f85]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_47,plain,
% 7.28/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4096,plain,
% 7.28/1.52      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_4042,c_47]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_31,negated_conjecture,
% 7.28/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.28/1.52      inference(cnf_transformation,[],[f80]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1672,plain,
% 7.28/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_6,plain,
% 7.28/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.28/1.52      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.28/1.52      inference(cnf_transformation,[],[f91]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1690,plain,
% 7.28/1.52      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2731,plain,
% 7.28/1.52      ( k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1672,c_1690]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_27,negated_conjecture,
% 7.28/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.28/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1675,plain,
% 7.28/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4043,plain,
% 7.28/1.52      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 7.28/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1675,c_1683]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_29,negated_conjecture,
% 7.28/1.52      ( v1_funct_1(sK4) ),
% 7.28/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_44,plain,
% 7.28/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4137,plain,
% 7.28/1.52      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_4043,c_44]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_18,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.28/1.52      inference(cnf_transformation,[],[f96]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_22,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f72]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_21,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_20,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_209,plain,
% 7.28/1.52      ( ~ v1_funct_1(X3)
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_18,c_22,c_21,c_20]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_210,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_209]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1665,plain,
% 7.28/1.52      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 7.28/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.28/1.52      | v1_funct_2(X5,X4,X1) != iProver_top
% 7.28/1.52      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.28/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 7.28/1.52      | v1_funct_1(X2) != iProver_top
% 7.28/1.52      | v1_funct_1(X5) != iProver_top
% 7.28/1.52      | v1_xboole_0(X3) = iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X4) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4143,plain,
% 7.28/1.52      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 7.28/1.52      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.28/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | v1_funct_1(X1) != iProver_top
% 7.28/1.52      | v1_funct_1(sK4) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK1) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4137,c_1665]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_35,negated_conjecture,
% 7.28/1.52      ( ~ v1_xboole_0(sK1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f76]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_38,plain,
% 7.28/1.52      ( v1_xboole_0(sK1) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_34,negated_conjecture,
% 7.28/1.52      ( ~ v1_xboole_0(sK2) ),
% 7.28/1.52      inference(cnf_transformation,[],[f77]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_39,plain,
% 7.28/1.52      ( v1_xboole_0(sK2) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_28,negated_conjecture,
% 7.28/1.52      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_45,plain,
% 7.28/1.52      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_46,plain,
% 7.28/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9055,plain,
% 7.28/1.52      ( v1_funct_1(X1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.28/1.52      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 7.28/1.52      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_4143,c_38,c_39,c_44,c_45,c_46]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9056,plain,
% 7.28/1.52      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 7.28/1.52      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | v1_funct_1(X1) != iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_9055]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9069,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 7.28/1.52      | k2_partfun1(sK3,sK1,X0,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.28/1.52      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK3) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_2731,c_9056]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1,plain,
% 7.28/1.52      ( ~ r1_xboole_0(X0,X1)
% 7.28/1.52      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.28/1.52      inference(cnf_transformation,[],[f90]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_272,plain,
% 7.28/1.52      ( ~ r1_xboole_0(X0,X1)
% 7.28/1.52      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.28/1.52      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_14,plain,
% 7.28/1.52      ( ~ r1_subset_1(X0,X1)
% 7.28/1.52      | r1_xboole_0(X0,X1)
% 7.28/1.52      | v1_xboole_0(X0)
% 7.28/1.52      | v1_xboole_0(X1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_30,negated_conjecture,
% 7.28/1.52      ( r1_subset_1(sK2,sK3) ),
% 7.28/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_475,plain,
% 7.28/1.52      ( r1_xboole_0(X0,X1)
% 7.28/1.52      | v1_xboole_0(X0)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | sK3 != X1
% 7.28/1.52      | sK2 != X0 ),
% 7.28/1.52      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_476,plain,
% 7.28/1.52      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.28/1.52      inference(unflattening,[status(thm)],[c_475]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_32,negated_conjecture,
% 7.28/1.52      ( ~ v1_xboole_0(sK3) ),
% 7.28/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_478,plain,
% 7.28/1.52      ( r1_xboole_0(sK2,sK3) ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_476,c_34,c_32]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_533,plain,
% 7.28/1.52      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 7.28/1.52      | sK3 != X1
% 7.28/1.52      | sK2 != X0 ),
% 7.28/1.52      inference(resolution_lifted,[status(thm)],[c_272,c_478]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_534,plain,
% 7.28/1.52      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.28/1.52      inference(unflattening,[status(thm)],[c_533]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9080,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 7.28/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0,k1_xboole_0)
% 7.28/1.52      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK3) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_9069,c_534]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9081,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 7.28/1.52      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,X0,k1_xboole_0)
% 7.28/1.52      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK3) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_9080,c_2731]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_15,plain,
% 7.28/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | v1_relat_1(X0) ),
% 7.28/1.52      inference(cnf_transformation,[],[f67]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1684,plain,
% 7.28/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.28/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2725,plain,
% 7.28/1.52      ( v1_relat_1(sK4) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1675,c_1684]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4,plain,
% 7.28/1.52      ( r1_tarski(X0,X0) ),
% 7.28/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1691,plain,
% 7.28/1.52      ( r1_tarski(X0,X0) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_8,plain,
% 7.28/1.52      ( v4_relat_1(X0,X1)
% 7.28/1.52      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.28/1.52      | ~ v1_relat_1(X0) ),
% 7.28/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1688,plain,
% 7.28/1.52      ( v4_relat_1(X0,X1) = iProver_top
% 7.28/1.52      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.28/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4036,plain,
% 7.28/1.52      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 7.28/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1691,c_1688]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_12,plain,
% 7.28/1.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.28/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1685,plain,
% 7.28/1.52      ( k7_relat_1(X0,X1) = X0
% 7.28/1.52      | v4_relat_1(X0,X1) != iProver_top
% 7.28/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4751,plain,
% 7.28/1.52      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 7.28/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4036,c_1685]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4766,plain,
% 7.28/1.52      ( k7_relat_1(sK4,k1_relat_1(sK4)) = sK4 ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_2725,c_4751]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_11,plain,
% 7.28/1.52      ( ~ r1_xboole_0(X0,X1)
% 7.28/1.52      | ~ v1_relat_1(X2)
% 7.28/1.52      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.28/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_5,plain,
% 7.28/1.52      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.28/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_503,plain,
% 7.28/1.52      ( ~ v1_relat_1(X0)
% 7.28/1.52      | X1 != X2
% 7.28/1.52      | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
% 7.28/1.52      | k1_xboole_0 != X3 ),
% 7.28/1.52      inference(resolution_lifted,[status(thm)],[c_11,c_5]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_504,plain,
% 7.28/1.52      ( ~ v1_relat_1(X0)
% 7.28/1.52      | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 7.28/1.52      inference(unflattening,[status(thm)],[c_503]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1663,plain,
% 7.28/1.52      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 7.28/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2898,plain,
% 7.28/1.52      ( k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_2725,c_1663]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4973,plain,
% 7.28/1.52      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4766,c_2898]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9082,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 7.28/1.52      | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
% 7.28/1.52      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK3) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_9081,c_534,c_4973]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_36,negated_conjecture,
% 7.28/1.52      ( ~ v1_xboole_0(sK0) ),
% 7.28/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_37,plain,
% 7.28/1.52      ( v1_xboole_0(sK0) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_33,negated_conjecture,
% 7.28/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.28/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_40,plain,
% 7.28/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_41,plain,
% 7.28/1.52      ( v1_xboole_0(sK3) != iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_42,plain,
% 7.28/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9133,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0),sK3) = X0
% 7.28/1.52      | k2_partfun1(sK3,sK1,X0,k1_xboole_0) != k1_xboole_0
% 7.28/1.52      | v1_funct_2(X0,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_9082,c_37,c_40,c_41,c_42]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9139,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.28/1.52      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.28/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4096,c_9133]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2724,plain,
% 7.28/1.52      ( v1_relat_1(sK5) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1678,c_1684]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4765,plain,
% 7.28/1.52      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_2724,c_4751]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2894,plain,
% 7.28/1.52      ( k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_2724,c_1663]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4972,plain,
% 7.28/1.52      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4765,c_2894]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9140,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.28/1.52      | k1_xboole_0 != k1_xboole_0
% 7.28/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_9139,c_4972]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9141,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.28/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.28/1.52      inference(equality_resolution_simp,[status(thm)],[c_9140]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1679,plain,
% 7.28/1.52      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.28/1.52      | v1_funct_2(X3,X4,X2) != iProver_top
% 7.28/1.52      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.28/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top
% 7.28/1.52      | v1_funct_1(X3) != iProver_top
% 7.28/1.52      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0)) = iProver_top
% 7.28/1.52      | v1_xboole_0(X5) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top
% 7.28/1.52      | v1_xboole_0(X4) = iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1681,plain,
% 7.28/1.52      ( v1_funct_2(X0,X1,X2) != iProver_top
% 7.28/1.52      | v1_funct_2(X3,X4,X2) != iProver_top
% 7.28/1.52      | m1_subset_1(X4,k1_zfmisc_1(X5)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X5)) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.28/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 7.28/1.52      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2))) = iProver_top
% 7.28/1.52      | v1_funct_1(X0) != iProver_top
% 7.28/1.52      | v1_funct_1(X3) != iProver_top
% 7.28/1.52      | v1_xboole_0(X5) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top
% 7.28/1.52      | v1_xboole_0(X4) = iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4410,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 7.28/1.52      | v1_funct_2(X5,X2,X3) != iProver_top
% 7.28/1.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.28/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.28/1.52      | v1_funct_1(X5) != iProver_top
% 7.28/1.52      | v1_funct_1(X4) != iProver_top
% 7.28/1.52      | v1_funct_1(k1_tmap_1(X0,X3,X1,X2,X4,X5)) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(X3) = iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1681,c_1683]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7259,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,X1,X2),X3,k1_tmap_1(X0,X3,X1,X2,X4,X5),X6) = k7_relat_1(k1_tmap_1(X0,X3,X1,X2,X4,X5),X6)
% 7.28/1.52      | v1_funct_2(X5,X2,X3) != iProver_top
% 7.28/1.52      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.28/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.28/1.52      | v1_funct_1(X5) != iProver_top
% 7.28/1.52      | v1_funct_1(X4) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(X3) = iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1679,c_4410]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7275,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
% 7.28/1.52      | v1_funct_2(X2,X1,sK1) != iProver_top
% 7.28/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | v1_funct_1(X2) != iProver_top
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK1) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1678,c_7259]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_25,negated_conjecture,
% 7.28/1.52      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.28/1.52      inference(cnf_transformation,[],[f86]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_48,plain,
% 7.28/1.52      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7287,plain,
% 7.28/1.52      ( v1_funct_1(X2) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
% 7.28/1.52      | v1_funct_2(X2,X1,sK1) != iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_7275,c_38,c_41,c_47,c_48]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7288,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,X1,sK3),sK1,k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3) = k7_relat_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5),X3)
% 7.28/1.52      | v1_funct_2(X2,X1,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | v1_funct_1(X2) != iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_7287]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7295,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
% 7.28/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | v1_funct_1(sK4) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1675,c_7288]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7437,plain,
% 7.28/1.52      ( v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_7295,c_39,c_44,c_45]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7438,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1) = k7_relat_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),X1)
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_7437]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7443,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0)
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_1672,c_7438]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7448,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0) ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_7443,c_37,c_40]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_9142,plain,
% 7.28/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.28/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_9141,c_7448]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_23,negated_conjecture,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.28/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2931,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_2731,c_23]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_2932,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_2931,c_534]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4099,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_4096,c_2932]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4511,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_4099,c_4137]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7451,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_7448,c_4511]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7455,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_7451,c_4972,c_4973]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7456,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.28/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.28/1.52      inference(equality_resolution_simp,[status(thm)],[c_7455]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7457,plain,
% 7.28/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.28/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_7456,c_7448]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_19,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.28/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_202,plain,
% 7.28/1.52      ( ~ v1_funct_1(X3)
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_19,c_22,c_21,c_20]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_203,plain,
% 7.28/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.28/1.52      | ~ v1_funct_2(X3,X4,X2)
% 7.28/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.28/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.28/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.28/1.52      | ~ v1_funct_1(X0)
% 7.28/1.52      | ~ v1_funct_1(X3)
% 7.28/1.52      | v1_xboole_0(X1)
% 7.28/1.52      | v1_xboole_0(X2)
% 7.28/1.52      | v1_xboole_0(X4)
% 7.28/1.52      | v1_xboole_0(X5)
% 7.28/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_202]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_1666,plain,
% 7.28/1.52      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 7.28/1.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.28/1.52      | v1_funct_2(X5,X4,X1) != iProver_top
% 7.28/1.52      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 7.28/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.28/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 7.28/1.52      | v1_funct_1(X2) != iProver_top
% 7.28/1.52      | v1_funct_1(X5) != iProver_top
% 7.28/1.52      | v1_xboole_0(X3) = iProver_top
% 7.28/1.52      | v1_xboole_0(X1) = iProver_top
% 7.28/1.52      | v1_xboole_0(X4) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4100,plain,
% 7.28/1.52      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 7.28/1.52      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.28/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | v1_funct_1(X1) != iProver_top
% 7.28/1.52      | v1_funct_1(sK5) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK1) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4096,c_1666]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_49,plain,
% 7.28/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.28/1.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4513,plain,
% 7.28/1.52      ( v1_funct_1(X1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.28/1.52      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 7.28/1.52      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_4100,c_38,c_41,c_47,c_48,c_49]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4514,plain,
% 7.28/1.52      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 7.28/1.52      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 7.28/1.52      | v1_funct_2(X1,X0,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 7.28/1.52      | v1_funct_1(X1) != iProver_top
% 7.28/1.52      | v1_xboole_0(X2) = iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_4513]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4520,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.28/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.28/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | v1_funct_1(sK4) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_4137,c_4514]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4636,plain,
% 7.28/1.52      ( v1_xboole_0(X0) = iProver_top
% 7.28/1.52      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_4520,c_39,c_44,c_45,c_46]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4637,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(X0) = iProver_top ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_4636]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4642,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(superposition,[status(thm)],[c_2731,c_4637]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4643,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_4642,c_534]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4644,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_4643,c_2731]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4645,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.28/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.28/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_4644,c_534]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4646,plain,
% 7.28/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.28/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.28/1.52      | v1_xboole_0(sK0)
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.28/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_4645]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4648,plain,
% 7.28/1.52      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.28/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.28/1.52      inference(global_propositional_subsumption,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_4645,c_36,c_33,c_31,c_4646]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_4649,plain,
% 7.28/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.28/1.52      inference(renaming,[status(thm)],[c_4648]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7452,plain,
% 7.28/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.28/1.52      inference(demodulation,[status(thm)],[c_7448,c_4649]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7453,plain,
% 7.28/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.28/1.52      | k1_xboole_0 != k1_xboole_0 ),
% 7.28/1.52      inference(light_normalisation,[status(thm)],[c_7452,c_4972,c_4973]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(c_7454,plain,
% 7.28/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.28/1.52      inference(equality_resolution_simp,[status(thm)],[c_7453]) ).
% 7.28/1.52  
% 7.28/1.52  cnf(contradiction,plain,
% 7.28/1.52      ( $false ),
% 7.28/1.52      inference(minisat,
% 7.28/1.52                [status(thm)],
% 7.28/1.52                [c_9142,c_7457,c_7454,c_49,c_48,c_47]) ).
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.28/1.52  
% 7.28/1.52  ------                               Statistics
% 7.28/1.52  
% 7.28/1.52  ------ General
% 7.28/1.52  
% 7.28/1.52  abstr_ref_over_cycles:                  0
% 7.28/1.52  abstr_ref_under_cycles:                 0
% 7.28/1.52  gc_basic_clause_elim:                   0
% 7.28/1.52  forced_gc_time:                         0
% 7.28/1.52  parsing_time:                           0.02
% 7.28/1.52  unif_index_cands_time:                  0.
% 7.28/1.52  unif_index_add_time:                    0.
% 7.28/1.52  orderings_time:                         0.
% 7.28/1.52  out_proof_time:                         0.018
% 7.28/1.52  total_time:                             0.737
% 7.28/1.52  num_of_symbols:                         57
% 7.28/1.52  num_of_terms:                           27304
% 7.28/1.52  
% 7.28/1.52  ------ Preprocessing
% 7.28/1.52  
% 7.28/1.52  num_of_splits:                          0
% 7.28/1.52  num_of_split_atoms:                     0
% 7.28/1.52  num_of_reused_defs:                     0
% 7.28/1.52  num_eq_ax_congr_red:                    16
% 7.28/1.52  num_of_sem_filtered_clauses:            1
% 7.28/1.52  num_of_subtypes:                        0
% 7.28/1.52  monotx_restored_types:                  0
% 7.28/1.52  sat_num_of_epr_types:                   0
% 7.28/1.52  sat_num_of_non_cyclic_types:            0
% 7.28/1.52  sat_guarded_non_collapsed_types:        0
% 7.28/1.52  num_pure_diseq_elim:                    0
% 7.28/1.52  simp_replaced_by:                       0
% 7.28/1.52  res_preprocessed:                       173
% 7.28/1.52  prep_upred:                             0
% 7.28/1.52  prep_unflattend:                        24
% 7.28/1.52  smt_new_axioms:                         0
% 7.28/1.52  pred_elim_cands:                        7
% 7.28/1.52  pred_elim:                              2
% 7.28/1.52  pred_elim_cl:                           2
% 7.28/1.52  pred_elim_cycles:                       4
% 7.28/1.52  merged_defs:                            2
% 7.28/1.52  merged_defs_ncl:                        0
% 7.28/1.52  bin_hyper_res:                          2
% 7.28/1.52  prep_cycles:                            4
% 7.28/1.52  pred_elim_time:                         0.012
% 7.28/1.52  splitting_time:                         0.
% 7.28/1.52  sem_filter_time:                        0.
% 7.28/1.52  monotx_time:                            0.001
% 7.28/1.52  subtype_inf_time:                       0.
% 7.28/1.52  
% 7.28/1.52  ------ Problem properties
% 7.28/1.52  
% 7.28/1.52  clauses:                                34
% 7.28/1.52  conjectures:                            13
% 7.28/1.52  epr:                                    10
% 7.28/1.52  horn:                                   28
% 7.28/1.52  ground:                                 14
% 7.28/1.52  unary:                                  16
% 7.28/1.52  binary:                                 4
% 7.28/1.52  lits:                                   133
% 7.28/1.52  lits_eq:                                19
% 7.28/1.52  fd_pure:                                0
% 7.28/1.52  fd_pseudo:                              0
% 7.28/1.52  fd_cond:                                0
% 7.28/1.52  fd_pseudo_cond:                         1
% 7.28/1.52  ac_symbols:                             0
% 7.28/1.52  
% 7.28/1.52  ------ Propositional Solver
% 7.28/1.52  
% 7.28/1.52  prop_solver_calls:                      28
% 7.28/1.52  prop_fast_solver_calls:                 3031
% 7.28/1.52  smt_solver_calls:                       0
% 7.28/1.52  smt_fast_solver_calls:                  0
% 7.28/1.52  prop_num_of_clauses:                    5283
% 7.28/1.52  prop_preprocess_simplified:             10880
% 7.28/1.52  prop_fo_subsumed:                       228
% 7.28/1.52  prop_solver_time:                       0.
% 7.28/1.52  smt_solver_time:                        0.
% 7.28/1.52  smt_fast_solver_time:                   0.
% 7.28/1.52  prop_fast_solver_time:                  0.
% 7.28/1.52  prop_unsat_core_time:                   0.
% 7.28/1.52  
% 7.28/1.52  ------ QBF
% 7.28/1.52  
% 7.28/1.52  qbf_q_res:                              0
% 7.28/1.52  qbf_num_tautologies:                    0
% 7.28/1.52  qbf_prep_cycles:                        0
% 7.28/1.52  
% 7.28/1.52  ------ BMC1
% 7.28/1.52  
% 7.28/1.52  bmc1_current_bound:                     -1
% 7.28/1.52  bmc1_last_solved_bound:                 -1
% 7.28/1.52  bmc1_unsat_core_size:                   -1
% 7.28/1.52  bmc1_unsat_core_parents_size:           -1
% 7.28/1.52  bmc1_merge_next_fun:                    0
% 7.28/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.28/1.52  
% 7.28/1.52  ------ Instantiation
% 7.28/1.52  
% 7.28/1.52  inst_num_of_clauses:                    1083
% 7.28/1.52  inst_num_in_passive:                    90
% 7.28/1.52  inst_num_in_active:                     672
% 7.28/1.52  inst_num_in_unprocessed:                321
% 7.28/1.52  inst_num_of_loops:                      810
% 7.28/1.52  inst_num_of_learning_restarts:          0
% 7.28/1.52  inst_num_moves_active_passive:          136
% 7.28/1.52  inst_lit_activity:                      0
% 7.28/1.52  inst_lit_activity_moves:                1
% 7.28/1.52  inst_num_tautologies:                   0
% 7.28/1.52  inst_num_prop_implied:                  0
% 7.28/1.52  inst_num_existing_simplified:           0
% 7.28/1.52  inst_num_eq_res_simplified:             0
% 7.28/1.52  inst_num_child_elim:                    0
% 7.28/1.52  inst_num_of_dismatching_blockings:      73
% 7.28/1.52  inst_num_of_non_proper_insts:           962
% 7.28/1.52  inst_num_of_duplicates:                 0
% 7.28/1.52  inst_inst_num_from_inst_to_res:         0
% 7.28/1.52  inst_dismatching_checking_time:         0.
% 7.28/1.52  
% 7.28/1.52  ------ Resolution
% 7.28/1.52  
% 7.28/1.52  res_num_of_clauses:                     0
% 7.28/1.52  res_num_in_passive:                     0
% 7.28/1.52  res_num_in_active:                      0
% 7.28/1.52  res_num_of_loops:                       177
% 7.28/1.52  res_forward_subset_subsumed:            19
% 7.28/1.52  res_backward_subset_subsumed:           0
% 7.28/1.52  res_forward_subsumed:                   0
% 7.28/1.52  res_backward_subsumed:                  0
% 7.28/1.52  res_forward_subsumption_resolution:     0
% 7.28/1.52  res_backward_subsumption_resolution:    0
% 7.28/1.52  res_clause_to_clause_subsumption:       792
% 7.28/1.52  res_orphan_elimination:                 0
% 7.28/1.52  res_tautology_del:                      19
% 7.28/1.52  res_num_eq_res_simplified:              0
% 7.28/1.52  res_num_sel_changes:                    0
% 7.28/1.52  res_moves_from_active_to_pass:          0
% 7.28/1.52  
% 7.28/1.52  ------ Superposition
% 7.28/1.52  
% 7.28/1.52  sup_time_total:                         0.
% 7.28/1.52  sup_time_generating:                    0.
% 7.28/1.52  sup_time_sim_full:                      0.
% 7.28/1.52  sup_time_sim_immed:                     0.
% 7.28/1.52  
% 7.28/1.52  sup_num_of_clauses:                     301
% 7.28/1.52  sup_num_in_active:                      146
% 7.28/1.52  sup_num_in_passive:                     155
% 7.28/1.52  sup_num_of_loops:                       160
% 7.28/1.52  sup_fw_superposition:                   218
% 7.28/1.52  sup_bw_superposition:                   130
% 7.28/1.52  sup_immediate_simplified:               131
% 7.28/1.52  sup_given_eliminated:                   0
% 7.28/1.52  comparisons_done:                       0
% 7.28/1.52  comparisons_avoided:                    0
% 7.28/1.52  
% 7.28/1.52  ------ Simplifications
% 7.28/1.52  
% 7.28/1.52  
% 7.28/1.52  sim_fw_subset_subsumed:                 5
% 7.28/1.52  sim_bw_subset_subsumed:                 4
% 7.28/1.52  sim_fw_subsumed:                        23
% 7.28/1.52  sim_bw_subsumed:                        7
% 7.28/1.52  sim_fw_subsumption_res:                 0
% 7.28/1.52  sim_bw_subsumption_res:                 0
% 7.28/1.52  sim_tautology_del:                      1
% 7.28/1.52  sim_eq_tautology_del:                   8
% 7.28/1.52  sim_eq_res_simp:                        8
% 7.28/1.52  sim_fw_demodulated:                     77
% 7.28/1.52  sim_bw_demodulated:                     6
% 7.28/1.52  sim_light_normalised:                   51
% 7.28/1.52  sim_joinable_taut:                      0
% 7.28/1.52  sim_joinable_simp:                      0
% 7.28/1.52  sim_ac_normalised:                      0
% 7.28/1.52  sim_smt_subsumption:                    0
% 7.28/1.52  
%------------------------------------------------------------------------------
