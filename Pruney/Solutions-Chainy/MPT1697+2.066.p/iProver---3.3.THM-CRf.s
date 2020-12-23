%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:37 EST 2020

% Result     : Theorem 6.99s
% Output     : CNFRefutation 6.99s
% Verified   : 
% Statistics : Number of formulae       :  212 (3017 expanded)
%              Number of clauses        :  140 ( 747 expanded)
%              Number of leaves         :   18 (1196 expanded)
%              Depth                    :   27
%              Number of atoms          : 1208 (39782 expanded)
%              Number of equality atoms :  501 (9501 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f41,f40,f39,f38,f37,f36])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f11,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f60,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f73,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_782,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1270,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_782])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1257,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_796])).

cnf(c_2450,plain,
    ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1270,c_1257])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_785,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1267,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1259,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_2507,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1259])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1652,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1836,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_2846,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_23,c_21,c_1836])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_788,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1264,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2506,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1259])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1647,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
    inference(instantiation,[status(thm)],[c_794])).

cnf(c_1827,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_2841,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_20,c_18,c_1827])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_177,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_16,c_15,c_14])).

cnf(c_178,plain,
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
    inference(renaming,[status(thm)],[c_177])).

cnf(c_775,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51)
    | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
    | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_178])).

cnf(c_1277,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
    | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_6720,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_1277])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_16904,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6720,c_32,c_35,c_41,c_42,c_43])).

cnf(c_16905,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_16904])).

cnf(c_16920,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_16905])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17486,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16920,c_33,c_38,c_39,c_40])).

cnf(c_17487,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_17486])).

cnf(c_17497,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_17487])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_230,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_444,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_445,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_447,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_28,c_26])).

cnf(c_502,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_447])).

cnf(c_503,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_769,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_503])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_9,c_8,c_5])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k7_relat_1(X0_51,X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1278,plain,
    ( k7_relat_1(X0_51,X1_51) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_10256,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_1264,c_1278])).

cnf(c_795,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1258,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_795])).

cnf(c_2226,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1258])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_472,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_2])).

cnf(c_473,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_772,plain,
    ( ~ v1_relat_1(X0_51)
    | k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_473])).

cnf(c_1280,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_2379,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0_51),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2226,c_1280])).

cnf(c_10801,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10256,c_2379])).

cnf(c_17498,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17497,c_769,c_10801])).

cnf(c_792,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1261,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_xboole_0(X5_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_792])).

cnf(c_2605,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
    | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1259])).

cnf(c_790,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1263,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
    | v1_xboole_0(X5_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_5421,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
    | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2605,c_1263])).

cnf(c_5425,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_5421])).

cnf(c_5586,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5425,c_32,c_35,c_41,c_42])).

cnf(c_5587,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_5586])).

cnf(c_5601,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_5587])).

cnf(c_5812,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5601,c_33,c_38,c_39])).

cnf(c_5813,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_5812])).

cnf(c_5822,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1270,c_5813])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5879,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5822,c_31,c_34])).

cnf(c_17499,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17498,c_2450,c_5879])).

cnf(c_10257,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_1267,c_1278])).

cnf(c_2227,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1258])).

cnf(c_2388,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0_51),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2227,c_1280])).

cnf(c_10804,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10257,c_2388])).

cnf(c_17500,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17499,c_769,c_10804])).

cnf(c_17501,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17500])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f77])).

cnf(c_170,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_16,c_15,c_14])).

cnf(c_171,plain,
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
    inference(renaming,[status(thm)],[c_170])).

cnf(c_776,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51)
    | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
    | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
    inference(subtyping,[status(esa)],[c_171])).

cnf(c_1276,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
    | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_4693,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_1276])).

cnf(c_8548,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4693,c_32,c_35,c_41,c_42,c_43])).

cnf(c_8549,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_8548])).

cnf(c_8564,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2846,c_8549])).

cnf(c_9006,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8564,c_33,c_38,c_39,c_40])).

cnf(c_9007,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_9006])).

cnf(c_9017,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2450,c_9007])).

cnf(c_9018,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9017,c_769])).

cnf(c_9019,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9018,c_2450,c_5879])).

cnf(c_9020,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9019,c_769])).

cnf(c_9021,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9020])).

cnf(c_10249,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9020,c_30,c_27,c_25,c_9021])).

cnf(c_10250,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_10249])).

cnf(c_11843,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10801,c_10250])).

cnf(c_17,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_789,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2740,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2450,c_789])).

cnf(c_2741,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2740,c_769])).

cnf(c_2944,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2741,c_2841,c_2846])).

cnf(c_5883,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5879,c_2944])).

cnf(c_5884,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5883,c_5879])).

cnf(c_11844,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10801,c_5884])).

cnf(c_11854,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11843,c_11844])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17501,c_11854,c_10804,c_36,c_34,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.99/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.99/1.51  
% 6.99/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.99/1.51  
% 6.99/1.51  ------  iProver source info
% 6.99/1.51  
% 6.99/1.51  git: date: 2020-06-30 10:37:57 +0100
% 6.99/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.99/1.51  git: non_committed_changes: false
% 6.99/1.51  git: last_make_outside_of_git: false
% 6.99/1.51  
% 6.99/1.51  ------ 
% 6.99/1.51  
% 6.99/1.51  ------ Input Options
% 6.99/1.51  
% 6.99/1.51  --out_options                           all
% 6.99/1.51  --tptp_safe_out                         true
% 6.99/1.51  --problem_path                          ""
% 6.99/1.51  --include_path                          ""
% 6.99/1.51  --clausifier                            res/vclausify_rel
% 6.99/1.51  --clausifier_options                    --mode clausify
% 6.99/1.51  --stdin                                 false
% 6.99/1.51  --stats_out                             all
% 6.99/1.51  
% 6.99/1.51  ------ General Options
% 6.99/1.51  
% 6.99/1.51  --fof                                   false
% 6.99/1.51  --time_out_real                         305.
% 6.99/1.51  --time_out_virtual                      -1.
% 6.99/1.51  --symbol_type_check                     false
% 6.99/1.51  --clausify_out                          false
% 6.99/1.51  --sig_cnt_out                           false
% 6.99/1.51  --trig_cnt_out                          false
% 6.99/1.51  --trig_cnt_out_tolerance                1.
% 6.99/1.51  --trig_cnt_out_sk_spl                   false
% 6.99/1.51  --abstr_cl_out                          false
% 6.99/1.51  
% 6.99/1.51  ------ Global Options
% 6.99/1.51  
% 6.99/1.51  --schedule                              default
% 6.99/1.51  --add_important_lit                     false
% 6.99/1.51  --prop_solver_per_cl                    1000
% 6.99/1.51  --min_unsat_core                        false
% 6.99/1.51  --soft_assumptions                      false
% 6.99/1.51  --soft_lemma_size                       3
% 6.99/1.51  --prop_impl_unit_size                   0
% 6.99/1.51  --prop_impl_unit                        []
% 6.99/1.51  --share_sel_clauses                     true
% 6.99/1.51  --reset_solvers                         false
% 6.99/1.51  --bc_imp_inh                            [conj_cone]
% 6.99/1.51  --conj_cone_tolerance                   3.
% 6.99/1.51  --extra_neg_conj                        none
% 6.99/1.51  --large_theory_mode                     true
% 6.99/1.51  --prolific_symb_bound                   200
% 6.99/1.51  --lt_threshold                          2000
% 6.99/1.51  --clause_weak_htbl                      true
% 6.99/1.51  --gc_record_bc_elim                     false
% 6.99/1.51  
% 6.99/1.51  ------ Preprocessing Options
% 6.99/1.51  
% 6.99/1.51  --preprocessing_flag                    true
% 6.99/1.51  --time_out_prep_mult                    0.1
% 6.99/1.51  --splitting_mode                        input
% 6.99/1.51  --splitting_grd                         true
% 6.99/1.51  --splitting_cvd                         false
% 6.99/1.51  --splitting_cvd_svl                     false
% 6.99/1.51  --splitting_nvd                         32
% 6.99/1.51  --sub_typing                            true
% 6.99/1.51  --prep_gs_sim                           true
% 6.99/1.51  --prep_unflatten                        true
% 6.99/1.51  --prep_res_sim                          true
% 6.99/1.51  --prep_upred                            true
% 6.99/1.51  --prep_sem_filter                       exhaustive
% 6.99/1.51  --prep_sem_filter_out                   false
% 6.99/1.51  --pred_elim                             true
% 6.99/1.51  --res_sim_input                         true
% 6.99/1.51  --eq_ax_congr_red                       true
% 6.99/1.51  --pure_diseq_elim                       true
% 6.99/1.51  --brand_transform                       false
% 6.99/1.51  --non_eq_to_eq                          false
% 6.99/1.51  --prep_def_merge                        true
% 6.99/1.51  --prep_def_merge_prop_impl              false
% 6.99/1.51  --prep_def_merge_mbd                    true
% 6.99/1.51  --prep_def_merge_tr_red                 false
% 6.99/1.51  --prep_def_merge_tr_cl                  false
% 6.99/1.51  --smt_preprocessing                     true
% 6.99/1.51  --smt_ac_axioms                         fast
% 6.99/1.51  --preprocessed_out                      false
% 6.99/1.51  --preprocessed_stats                    false
% 6.99/1.51  
% 6.99/1.51  ------ Abstraction refinement Options
% 6.99/1.51  
% 6.99/1.51  --abstr_ref                             []
% 6.99/1.51  --abstr_ref_prep                        false
% 6.99/1.51  --abstr_ref_until_sat                   false
% 6.99/1.51  --abstr_ref_sig_restrict                funpre
% 6.99/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.99/1.51  --abstr_ref_under                       []
% 6.99/1.51  
% 6.99/1.51  ------ SAT Options
% 6.99/1.51  
% 6.99/1.51  --sat_mode                              false
% 6.99/1.51  --sat_fm_restart_options                ""
% 6.99/1.51  --sat_gr_def                            false
% 6.99/1.51  --sat_epr_types                         true
% 6.99/1.51  --sat_non_cyclic_types                  false
% 6.99/1.51  --sat_finite_models                     false
% 6.99/1.51  --sat_fm_lemmas                         false
% 6.99/1.51  --sat_fm_prep                           false
% 6.99/1.51  --sat_fm_uc_incr                        true
% 6.99/1.51  --sat_out_model                         small
% 6.99/1.51  --sat_out_clauses                       false
% 6.99/1.51  
% 6.99/1.51  ------ QBF Options
% 6.99/1.51  
% 6.99/1.51  --qbf_mode                              false
% 6.99/1.51  --qbf_elim_univ                         false
% 6.99/1.51  --qbf_dom_inst                          none
% 6.99/1.51  --qbf_dom_pre_inst                      false
% 6.99/1.51  --qbf_sk_in                             false
% 6.99/1.51  --qbf_pred_elim                         true
% 6.99/1.51  --qbf_split                             512
% 6.99/1.51  
% 6.99/1.51  ------ BMC1 Options
% 6.99/1.51  
% 6.99/1.51  --bmc1_incremental                      false
% 6.99/1.51  --bmc1_axioms                           reachable_all
% 6.99/1.51  --bmc1_min_bound                        0
% 6.99/1.51  --bmc1_max_bound                        -1
% 6.99/1.51  --bmc1_max_bound_default                -1
% 6.99/1.51  --bmc1_symbol_reachability              true
% 6.99/1.51  --bmc1_property_lemmas                  false
% 6.99/1.51  --bmc1_k_induction                      false
% 6.99/1.51  --bmc1_non_equiv_states                 false
% 6.99/1.51  --bmc1_deadlock                         false
% 6.99/1.51  --bmc1_ucm                              false
% 6.99/1.51  --bmc1_add_unsat_core                   none
% 6.99/1.51  --bmc1_unsat_core_children              false
% 6.99/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.99/1.51  --bmc1_out_stat                         full
% 6.99/1.51  --bmc1_ground_init                      false
% 6.99/1.51  --bmc1_pre_inst_next_state              false
% 6.99/1.51  --bmc1_pre_inst_state                   false
% 6.99/1.51  --bmc1_pre_inst_reach_state             false
% 6.99/1.51  --bmc1_out_unsat_core                   false
% 6.99/1.51  --bmc1_aig_witness_out                  false
% 6.99/1.51  --bmc1_verbose                          false
% 6.99/1.51  --bmc1_dump_clauses_tptp                false
% 6.99/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.99/1.51  --bmc1_dump_file                        -
% 6.99/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.99/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.99/1.51  --bmc1_ucm_extend_mode                  1
% 6.99/1.51  --bmc1_ucm_init_mode                    2
% 6.99/1.51  --bmc1_ucm_cone_mode                    none
% 6.99/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.99/1.51  --bmc1_ucm_relax_model                  4
% 6.99/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.99/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.99/1.51  --bmc1_ucm_layered_model                none
% 6.99/1.51  --bmc1_ucm_max_lemma_size               10
% 6.99/1.51  
% 6.99/1.51  ------ AIG Options
% 6.99/1.51  
% 6.99/1.51  --aig_mode                              false
% 6.99/1.51  
% 6.99/1.51  ------ Instantiation Options
% 6.99/1.51  
% 6.99/1.51  --instantiation_flag                    true
% 6.99/1.51  --inst_sos_flag                         false
% 6.99/1.51  --inst_sos_phase                        true
% 6.99/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.99/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.99/1.51  --inst_lit_sel_side                     num_symb
% 6.99/1.51  --inst_solver_per_active                1400
% 6.99/1.51  --inst_solver_calls_frac                1.
% 6.99/1.51  --inst_passive_queue_type               priority_queues
% 6.99/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.99/1.51  --inst_passive_queues_freq              [25;2]
% 6.99/1.51  --inst_dismatching                      true
% 6.99/1.51  --inst_eager_unprocessed_to_passive     true
% 6.99/1.51  --inst_prop_sim_given                   true
% 6.99/1.51  --inst_prop_sim_new                     false
% 6.99/1.51  --inst_subs_new                         false
% 6.99/1.51  --inst_eq_res_simp                      false
% 6.99/1.51  --inst_subs_given                       false
% 6.99/1.51  --inst_orphan_elimination               true
% 6.99/1.51  --inst_learning_loop_flag               true
% 6.99/1.51  --inst_learning_start                   3000
% 6.99/1.51  --inst_learning_factor                  2
% 6.99/1.51  --inst_start_prop_sim_after_learn       3
% 6.99/1.51  --inst_sel_renew                        solver
% 6.99/1.51  --inst_lit_activity_flag                true
% 6.99/1.51  --inst_restr_to_given                   false
% 6.99/1.51  --inst_activity_threshold               500
% 6.99/1.51  --inst_out_proof                        true
% 6.99/1.51  
% 6.99/1.51  ------ Resolution Options
% 6.99/1.51  
% 6.99/1.51  --resolution_flag                       true
% 6.99/1.51  --res_lit_sel                           adaptive
% 6.99/1.51  --res_lit_sel_side                      none
% 6.99/1.51  --res_ordering                          kbo
% 6.99/1.51  --res_to_prop_solver                    active
% 6.99/1.51  --res_prop_simpl_new                    false
% 6.99/1.51  --res_prop_simpl_given                  true
% 6.99/1.51  --res_passive_queue_type                priority_queues
% 6.99/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.99/1.51  --res_passive_queues_freq               [15;5]
% 6.99/1.51  --res_forward_subs                      full
% 6.99/1.51  --res_backward_subs                     full
% 6.99/1.51  --res_forward_subs_resolution           true
% 6.99/1.51  --res_backward_subs_resolution          true
% 6.99/1.51  --res_orphan_elimination                true
% 6.99/1.51  --res_time_limit                        2.
% 6.99/1.51  --res_out_proof                         true
% 6.99/1.51  
% 6.99/1.51  ------ Superposition Options
% 6.99/1.51  
% 6.99/1.51  --superposition_flag                    true
% 6.99/1.51  --sup_passive_queue_type                priority_queues
% 6.99/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.99/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.99/1.51  --demod_completeness_check              fast
% 6.99/1.51  --demod_use_ground                      true
% 6.99/1.51  --sup_to_prop_solver                    passive
% 6.99/1.51  --sup_prop_simpl_new                    true
% 6.99/1.51  --sup_prop_simpl_given                  true
% 6.99/1.51  --sup_fun_splitting                     false
% 6.99/1.51  --sup_smt_interval                      50000
% 6.99/1.51  
% 6.99/1.51  ------ Superposition Simplification Setup
% 6.99/1.51  
% 6.99/1.51  --sup_indices_passive                   []
% 6.99/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.99/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.51  --sup_full_bw                           [BwDemod]
% 6.99/1.51  --sup_immed_triv                        [TrivRules]
% 6.99/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.99/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.51  --sup_immed_bw_main                     []
% 6.99/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.99/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.51  
% 6.99/1.51  ------ Combination Options
% 6.99/1.51  
% 6.99/1.51  --comb_res_mult                         3
% 6.99/1.51  --comb_sup_mult                         2
% 6.99/1.51  --comb_inst_mult                        10
% 6.99/1.51  
% 6.99/1.51  ------ Debug Options
% 6.99/1.51  
% 6.99/1.51  --dbg_backtrace                         false
% 6.99/1.51  --dbg_dump_prop_clauses                 false
% 6.99/1.51  --dbg_dump_prop_clauses_file            -
% 6.99/1.51  --dbg_out_stat                          false
% 6.99/1.51  ------ Parsing...
% 6.99/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.99/1.51  
% 6.99/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.99/1.51  
% 6.99/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.99/1.51  
% 6.99/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.99/1.51  ------ Proving...
% 6.99/1.51  ------ Problem Properties 
% 6.99/1.51  
% 6.99/1.51  
% 6.99/1.51  clauses                                 28
% 6.99/1.51  conjectures                             13
% 6.99/1.51  EPR                                     8
% 6.99/1.51  Horn                                    22
% 6.99/1.51  unary                                   14
% 6.99/1.51  binary                                  5
% 6.99/1.51  lits                                    117
% 6.99/1.51  lits eq                                 18
% 6.99/1.51  fd_pure                                 0
% 6.99/1.51  fd_pseudo                               0
% 6.99/1.51  fd_cond                                 0
% 6.99/1.51  fd_pseudo_cond                          0
% 6.99/1.51  AC symbols                              0
% 6.99/1.51  
% 6.99/1.51  ------ Schedule dynamic 5 is on 
% 6.99/1.51  
% 6.99/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.99/1.51  
% 6.99/1.51  
% 6.99/1.51  ------ 
% 6.99/1.51  Current options:
% 6.99/1.51  ------ 
% 6.99/1.51  
% 6.99/1.51  ------ Input Options
% 6.99/1.51  
% 6.99/1.51  --out_options                           all
% 6.99/1.51  --tptp_safe_out                         true
% 6.99/1.51  --problem_path                          ""
% 6.99/1.51  --include_path                          ""
% 6.99/1.51  --clausifier                            res/vclausify_rel
% 6.99/1.51  --clausifier_options                    --mode clausify
% 6.99/1.51  --stdin                                 false
% 6.99/1.51  --stats_out                             all
% 6.99/1.51  
% 6.99/1.51  ------ General Options
% 6.99/1.51  
% 6.99/1.51  --fof                                   false
% 6.99/1.51  --time_out_real                         305.
% 6.99/1.51  --time_out_virtual                      -1.
% 6.99/1.51  --symbol_type_check                     false
% 6.99/1.51  --clausify_out                          false
% 6.99/1.51  --sig_cnt_out                           false
% 6.99/1.51  --trig_cnt_out                          false
% 6.99/1.51  --trig_cnt_out_tolerance                1.
% 6.99/1.51  --trig_cnt_out_sk_spl                   false
% 6.99/1.51  --abstr_cl_out                          false
% 6.99/1.51  
% 6.99/1.51  ------ Global Options
% 6.99/1.51  
% 6.99/1.51  --schedule                              default
% 6.99/1.51  --add_important_lit                     false
% 6.99/1.51  --prop_solver_per_cl                    1000
% 6.99/1.51  --min_unsat_core                        false
% 6.99/1.51  --soft_assumptions                      false
% 6.99/1.51  --soft_lemma_size                       3
% 6.99/1.51  --prop_impl_unit_size                   0
% 6.99/1.51  --prop_impl_unit                        []
% 6.99/1.51  --share_sel_clauses                     true
% 6.99/1.51  --reset_solvers                         false
% 6.99/1.51  --bc_imp_inh                            [conj_cone]
% 6.99/1.51  --conj_cone_tolerance                   3.
% 6.99/1.51  --extra_neg_conj                        none
% 6.99/1.51  --large_theory_mode                     true
% 6.99/1.51  --prolific_symb_bound                   200
% 6.99/1.51  --lt_threshold                          2000
% 6.99/1.51  --clause_weak_htbl                      true
% 6.99/1.51  --gc_record_bc_elim                     false
% 6.99/1.51  
% 6.99/1.51  ------ Preprocessing Options
% 6.99/1.51  
% 6.99/1.51  --preprocessing_flag                    true
% 6.99/1.51  --time_out_prep_mult                    0.1
% 6.99/1.51  --splitting_mode                        input
% 6.99/1.51  --splitting_grd                         true
% 6.99/1.51  --splitting_cvd                         false
% 6.99/1.51  --splitting_cvd_svl                     false
% 6.99/1.51  --splitting_nvd                         32
% 6.99/1.51  --sub_typing                            true
% 6.99/1.51  --prep_gs_sim                           true
% 6.99/1.51  --prep_unflatten                        true
% 6.99/1.51  --prep_res_sim                          true
% 6.99/1.51  --prep_upred                            true
% 6.99/1.51  --prep_sem_filter                       exhaustive
% 6.99/1.51  --prep_sem_filter_out                   false
% 6.99/1.51  --pred_elim                             true
% 6.99/1.51  --res_sim_input                         true
% 6.99/1.51  --eq_ax_congr_red                       true
% 6.99/1.51  --pure_diseq_elim                       true
% 6.99/1.51  --brand_transform                       false
% 6.99/1.51  --non_eq_to_eq                          false
% 6.99/1.51  --prep_def_merge                        true
% 6.99/1.51  --prep_def_merge_prop_impl              false
% 6.99/1.51  --prep_def_merge_mbd                    true
% 6.99/1.51  --prep_def_merge_tr_red                 false
% 6.99/1.51  --prep_def_merge_tr_cl                  false
% 6.99/1.51  --smt_preprocessing                     true
% 6.99/1.51  --smt_ac_axioms                         fast
% 6.99/1.51  --preprocessed_out                      false
% 6.99/1.51  --preprocessed_stats                    false
% 6.99/1.51  
% 6.99/1.51  ------ Abstraction refinement Options
% 6.99/1.51  
% 6.99/1.51  --abstr_ref                             []
% 6.99/1.51  --abstr_ref_prep                        false
% 6.99/1.51  --abstr_ref_until_sat                   false
% 6.99/1.51  --abstr_ref_sig_restrict                funpre
% 6.99/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.99/1.51  --abstr_ref_under                       []
% 6.99/1.51  
% 6.99/1.51  ------ SAT Options
% 6.99/1.51  
% 6.99/1.51  --sat_mode                              false
% 6.99/1.51  --sat_fm_restart_options                ""
% 6.99/1.51  --sat_gr_def                            false
% 6.99/1.51  --sat_epr_types                         true
% 6.99/1.51  --sat_non_cyclic_types                  false
% 6.99/1.51  --sat_finite_models                     false
% 6.99/1.51  --sat_fm_lemmas                         false
% 6.99/1.51  --sat_fm_prep                           false
% 6.99/1.51  --sat_fm_uc_incr                        true
% 6.99/1.51  --sat_out_model                         small
% 6.99/1.51  --sat_out_clauses                       false
% 6.99/1.51  
% 6.99/1.51  ------ QBF Options
% 6.99/1.51  
% 6.99/1.51  --qbf_mode                              false
% 6.99/1.51  --qbf_elim_univ                         false
% 6.99/1.51  --qbf_dom_inst                          none
% 6.99/1.51  --qbf_dom_pre_inst                      false
% 6.99/1.51  --qbf_sk_in                             false
% 6.99/1.51  --qbf_pred_elim                         true
% 6.99/1.51  --qbf_split                             512
% 6.99/1.51  
% 6.99/1.51  ------ BMC1 Options
% 6.99/1.51  
% 6.99/1.51  --bmc1_incremental                      false
% 6.99/1.51  --bmc1_axioms                           reachable_all
% 6.99/1.51  --bmc1_min_bound                        0
% 6.99/1.51  --bmc1_max_bound                        -1
% 6.99/1.51  --bmc1_max_bound_default                -1
% 6.99/1.51  --bmc1_symbol_reachability              true
% 6.99/1.51  --bmc1_property_lemmas                  false
% 6.99/1.51  --bmc1_k_induction                      false
% 6.99/1.51  --bmc1_non_equiv_states                 false
% 6.99/1.51  --bmc1_deadlock                         false
% 6.99/1.51  --bmc1_ucm                              false
% 6.99/1.51  --bmc1_add_unsat_core                   none
% 6.99/1.51  --bmc1_unsat_core_children              false
% 6.99/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.99/1.51  --bmc1_out_stat                         full
% 6.99/1.51  --bmc1_ground_init                      false
% 6.99/1.51  --bmc1_pre_inst_next_state              false
% 6.99/1.51  --bmc1_pre_inst_state                   false
% 6.99/1.51  --bmc1_pre_inst_reach_state             false
% 6.99/1.51  --bmc1_out_unsat_core                   false
% 6.99/1.51  --bmc1_aig_witness_out                  false
% 6.99/1.51  --bmc1_verbose                          false
% 6.99/1.51  --bmc1_dump_clauses_tptp                false
% 6.99/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.99/1.51  --bmc1_dump_file                        -
% 6.99/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.99/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.99/1.51  --bmc1_ucm_extend_mode                  1
% 6.99/1.51  --bmc1_ucm_init_mode                    2
% 6.99/1.51  --bmc1_ucm_cone_mode                    none
% 6.99/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.99/1.51  --bmc1_ucm_relax_model                  4
% 6.99/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.99/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.99/1.51  --bmc1_ucm_layered_model                none
% 6.99/1.51  --bmc1_ucm_max_lemma_size               10
% 6.99/1.51  
% 6.99/1.51  ------ AIG Options
% 6.99/1.51  
% 6.99/1.51  --aig_mode                              false
% 6.99/1.51  
% 6.99/1.51  ------ Instantiation Options
% 6.99/1.51  
% 6.99/1.51  --instantiation_flag                    true
% 6.99/1.51  --inst_sos_flag                         false
% 6.99/1.51  --inst_sos_phase                        true
% 6.99/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.99/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.99/1.51  --inst_lit_sel_side                     none
% 6.99/1.51  --inst_solver_per_active                1400
% 6.99/1.51  --inst_solver_calls_frac                1.
% 6.99/1.51  --inst_passive_queue_type               priority_queues
% 6.99/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.99/1.51  --inst_passive_queues_freq              [25;2]
% 6.99/1.51  --inst_dismatching                      true
% 6.99/1.51  --inst_eager_unprocessed_to_passive     true
% 6.99/1.51  --inst_prop_sim_given                   true
% 6.99/1.51  --inst_prop_sim_new                     false
% 6.99/1.51  --inst_subs_new                         false
% 6.99/1.51  --inst_eq_res_simp                      false
% 6.99/1.51  --inst_subs_given                       false
% 6.99/1.51  --inst_orphan_elimination               true
% 6.99/1.51  --inst_learning_loop_flag               true
% 6.99/1.51  --inst_learning_start                   3000
% 6.99/1.51  --inst_learning_factor                  2
% 6.99/1.51  --inst_start_prop_sim_after_learn       3
% 6.99/1.51  --inst_sel_renew                        solver
% 6.99/1.51  --inst_lit_activity_flag                true
% 6.99/1.51  --inst_restr_to_given                   false
% 6.99/1.51  --inst_activity_threshold               500
% 6.99/1.51  --inst_out_proof                        true
% 6.99/1.51  
% 6.99/1.51  ------ Resolution Options
% 6.99/1.51  
% 6.99/1.51  --resolution_flag                       false
% 6.99/1.51  --res_lit_sel                           adaptive
% 6.99/1.51  --res_lit_sel_side                      none
% 6.99/1.51  --res_ordering                          kbo
% 6.99/1.51  --res_to_prop_solver                    active
% 6.99/1.51  --res_prop_simpl_new                    false
% 6.99/1.51  --res_prop_simpl_given                  true
% 6.99/1.51  --res_passive_queue_type                priority_queues
% 6.99/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.99/1.51  --res_passive_queues_freq               [15;5]
% 6.99/1.51  --res_forward_subs                      full
% 6.99/1.51  --res_backward_subs                     full
% 6.99/1.51  --res_forward_subs_resolution           true
% 6.99/1.51  --res_backward_subs_resolution          true
% 6.99/1.51  --res_orphan_elimination                true
% 6.99/1.51  --res_time_limit                        2.
% 6.99/1.51  --res_out_proof                         true
% 6.99/1.51  
% 6.99/1.51  ------ Superposition Options
% 6.99/1.51  
% 6.99/1.51  --superposition_flag                    true
% 6.99/1.51  --sup_passive_queue_type                priority_queues
% 6.99/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.99/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.99/1.51  --demod_completeness_check              fast
% 6.99/1.51  --demod_use_ground                      true
% 6.99/1.51  --sup_to_prop_solver                    passive
% 6.99/1.51  --sup_prop_simpl_new                    true
% 6.99/1.51  --sup_prop_simpl_given                  true
% 6.99/1.51  --sup_fun_splitting                     false
% 6.99/1.51  --sup_smt_interval                      50000
% 6.99/1.51  
% 6.99/1.51  ------ Superposition Simplification Setup
% 6.99/1.51  
% 6.99/1.51  --sup_indices_passive                   []
% 6.99/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.99/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.99/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.51  --sup_full_bw                           [BwDemod]
% 6.99/1.51  --sup_immed_triv                        [TrivRules]
% 6.99/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.99/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.51  --sup_immed_bw_main                     []
% 6.99/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.99/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.99/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.99/1.51  
% 6.99/1.51  ------ Combination Options
% 6.99/1.51  
% 6.99/1.51  --comb_res_mult                         3
% 6.99/1.51  --comb_sup_mult                         2
% 6.99/1.51  --comb_inst_mult                        10
% 6.99/1.51  
% 6.99/1.51  ------ Debug Options
% 6.99/1.51  
% 6.99/1.51  --dbg_backtrace                         false
% 6.99/1.51  --dbg_dump_prop_clauses                 false
% 6.99/1.51  --dbg_dump_prop_clauses_file            -
% 6.99/1.51  --dbg_out_stat                          false
% 6.99/1.51  
% 6.99/1.51  
% 6.99/1.51  
% 6.99/1.51  
% 6.99/1.51  ------ Proving...
% 6.99/1.51  
% 6.99/1.51  
% 6.99/1.51  % SZS status Theorem for theBenchmark.p
% 6.99/1.51  
% 6.99/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.99/1.51  
% 6.99/1.51  fof(f12,conjecture,(
% 6.99/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f13,negated_conjecture,(
% 6.99/1.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.99/1.51    inference(negated_conjecture,[],[f12])).
% 6.99/1.51  
% 6.99/1.51  fof(f30,plain,(
% 6.99/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.99/1.51    inference(ennf_transformation,[],[f13])).
% 6.99/1.51  
% 6.99/1.51  fof(f31,plain,(
% 6.99/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.99/1.51    inference(flattening,[],[f30])).
% 6.99/1.51  
% 6.99/1.51  fof(f41,plain,(
% 6.99/1.51    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 6.99/1.51    introduced(choice_axiom,[])).
% 6.99/1.51  
% 6.99/1.51  fof(f40,plain,(
% 6.99/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 6.99/1.51    introduced(choice_axiom,[])).
% 6.99/1.51  
% 6.99/1.51  fof(f39,plain,(
% 6.99/1.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 6.99/1.51    introduced(choice_axiom,[])).
% 6.99/1.51  
% 6.99/1.51  fof(f38,plain,(
% 6.99/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 6.99/1.51    introduced(choice_axiom,[])).
% 6.99/1.51  
% 6.99/1.51  fof(f37,plain,(
% 6.99/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 6.99/1.51    introduced(choice_axiom,[])).
% 6.99/1.51  
% 6.99/1.51  fof(f36,plain,(
% 6.99/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 6.99/1.51    introduced(choice_axiom,[])).
% 6.99/1.51  
% 6.99/1.51  fof(f42,plain,(
% 6.99/1.51    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 6.99/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f41,f40,f39,f38,f37,f36])).
% 6.99/1.51  
% 6.99/1.51  fof(f65,plain,(
% 6.99/1.51    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f3,axiom,(
% 6.99/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f15,plain,(
% 6.99/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.99/1.51    inference(ennf_transformation,[],[f3])).
% 6.99/1.51  
% 6.99/1.51  fof(f46,plain,(
% 6.99/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.99/1.51    inference(cnf_transformation,[],[f15])).
% 6.99/1.51  
% 6.99/1.51  fof(f69,plain,(
% 6.99/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f9,axiom,(
% 6.99/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f24,plain,(
% 6.99/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.99/1.51    inference(ennf_transformation,[],[f9])).
% 6.99/1.51  
% 6.99/1.51  fof(f25,plain,(
% 6.99/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.99/1.51    inference(flattening,[],[f24])).
% 6.99/1.51  
% 6.99/1.51  fof(f53,plain,(
% 6.99/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f25])).
% 6.99/1.51  
% 6.99/1.51  fof(f67,plain,(
% 6.99/1.51    v1_funct_1(sK4)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f72,plain,(
% 6.99/1.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f70,plain,(
% 6.99/1.51    v1_funct_1(sK5)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f10,axiom,(
% 6.99/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f26,plain,(
% 6.99/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.51    inference(ennf_transformation,[],[f10])).
% 6.99/1.51  
% 6.99/1.51  fof(f27,plain,(
% 6.99/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.51    inference(flattening,[],[f26])).
% 6.99/1.51  
% 6.99/1.51  fof(f34,plain,(
% 6.99/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.51    inference(nnf_transformation,[],[f27])).
% 6.99/1.51  
% 6.99/1.51  fof(f35,plain,(
% 6.99/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.99/1.51    inference(flattening,[],[f34])).
% 6.99/1.51  
% 6.99/1.51  fof(f55,plain,(
% 6.99/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f35])).
% 6.99/1.51  
% 6.99/1.51  fof(f76,plain,(
% 6.99/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.51    inference(equality_resolution,[],[f55])).
% 6.99/1.51  
% 6.99/1.51  fof(f11,axiom,(
% 6.99/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f28,plain,(
% 6.99/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.99/1.51    inference(ennf_transformation,[],[f11])).
% 6.99/1.51  
% 6.99/1.51  fof(f29,plain,(
% 6.99/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.99/1.51    inference(flattening,[],[f28])).
% 6.99/1.51  
% 6.99/1.51  fof(f57,plain,(
% 6.99/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f29])).
% 6.99/1.51  
% 6.99/1.51  fof(f58,plain,(
% 6.99/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f29])).
% 6.99/1.51  
% 6.99/1.51  fof(f59,plain,(
% 6.99/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f29])).
% 6.99/1.51  
% 6.99/1.51  fof(f61,plain,(
% 6.99/1.51    ~v1_xboole_0(sK1)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f64,plain,(
% 6.99/1.51    ~v1_xboole_0(sK3)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f71,plain,(
% 6.99/1.51    v1_funct_2(sK5,sK3,sK1)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f62,plain,(
% 6.99/1.51    ~v1_xboole_0(sK2)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f68,plain,(
% 6.99/1.51    v1_funct_2(sK4,sK2,sK1)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f1,axiom,(
% 6.99/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f32,plain,(
% 6.99/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.99/1.51    inference(nnf_transformation,[],[f1])).
% 6.99/1.51  
% 6.99/1.51  fof(f43,plain,(
% 6.99/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f32])).
% 6.99/1.51  
% 6.99/1.51  fof(f6,axiom,(
% 6.99/1.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f20,plain,(
% 6.99/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.99/1.51    inference(ennf_transformation,[],[f6])).
% 6.99/1.51  
% 6.99/1.51  fof(f21,plain,(
% 6.99/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.99/1.51    inference(flattening,[],[f20])).
% 6.99/1.51  
% 6.99/1.51  fof(f33,plain,(
% 6.99/1.51    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.99/1.51    inference(nnf_transformation,[],[f21])).
% 6.99/1.51  
% 6.99/1.51  fof(f49,plain,(
% 6.99/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f33])).
% 6.99/1.51  
% 6.99/1.51  fof(f66,plain,(
% 6.99/1.51    r1_subset_1(sK2,sK3)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f8,axiom,(
% 6.99/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f14,plain,(
% 6.99/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.99/1.51    inference(pure_predicate_removal,[],[f8])).
% 6.99/1.51  
% 6.99/1.51  fof(f23,plain,(
% 6.99/1.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.51    inference(ennf_transformation,[],[f14])).
% 6.99/1.51  
% 6.99/1.51  fof(f52,plain,(
% 6.99/1.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.51    inference(cnf_transformation,[],[f23])).
% 6.99/1.51  
% 6.99/1.51  fof(f5,axiom,(
% 6.99/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f18,plain,(
% 6.99/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.99/1.51    inference(ennf_transformation,[],[f5])).
% 6.99/1.51  
% 6.99/1.51  fof(f19,plain,(
% 6.99/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.99/1.51    inference(flattening,[],[f18])).
% 6.99/1.51  
% 6.99/1.51  fof(f48,plain,(
% 6.99/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f19])).
% 6.99/1.51  
% 6.99/1.51  fof(f7,axiom,(
% 6.99/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f22,plain,(
% 6.99/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.99/1.51    inference(ennf_transformation,[],[f7])).
% 6.99/1.51  
% 6.99/1.51  fof(f51,plain,(
% 6.99/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.99/1.51    inference(cnf_transformation,[],[f22])).
% 6.99/1.51  
% 6.99/1.51  fof(f4,axiom,(
% 6.99/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f16,plain,(
% 6.99/1.51    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 6.99/1.51    inference(ennf_transformation,[],[f4])).
% 6.99/1.51  
% 6.99/1.51  fof(f17,plain,(
% 6.99/1.51    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 6.99/1.51    inference(flattening,[],[f16])).
% 6.99/1.51  
% 6.99/1.51  fof(f47,plain,(
% 6.99/1.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f17])).
% 6.99/1.51  
% 6.99/1.51  fof(f2,axiom,(
% 6.99/1.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.99/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.99/1.51  
% 6.99/1.51  fof(f45,plain,(
% 6.99/1.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.99/1.51    inference(cnf_transformation,[],[f2])).
% 6.99/1.51  
% 6.99/1.51  fof(f60,plain,(
% 6.99/1.51    ~v1_xboole_0(sK0)),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f63,plain,(
% 6.99/1.51    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.99/1.51    inference(cnf_transformation,[],[f42])).
% 6.99/1.51  
% 6.99/1.51  fof(f54,plain,(
% 6.99/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(cnf_transformation,[],[f35])).
% 6.99/1.52  
% 6.99/1.52  fof(f77,plain,(
% 6.99/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.99/1.52    inference(equality_resolution,[],[f54])).
% 6.99/1.52  
% 6.99/1.52  fof(f73,plain,(
% 6.99/1.52    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 6.99/1.52    inference(cnf_transformation,[],[f42])).
% 6.99/1.52  
% 6.99/1.52  cnf(c_25,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f65]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_782,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_25]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1270,plain,
% 6.99/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_782]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_3,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.99/1.52      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f46]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_796,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 6.99/1.52      | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_3]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1257,plain,
% 6.99/1.52      ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_796]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2450,plain,
% 6.99/1.52      ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1270,c_1257]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_21,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.99/1.52      inference(cnf_transformation,[],[f69]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_785,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_21]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1267,plain,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.99/1.52      inference(cnf_transformation,[],[f53]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_794,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | ~ v1_funct_1(X0_51)
% 6.99/1.52      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_10]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1259,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.99/1.52      | v1_funct_1(X2_51) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2507,plain,
% 6.99/1.52      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 6.99/1.52      | v1_funct_1(sK4) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1267,c_1259]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_23,negated_conjecture,
% 6.99/1.52      ( v1_funct_1(sK4) ),
% 6.99/1.52      inference(cnf_transformation,[],[f67]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1652,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 6.99/1.52      | ~ v1_funct_1(sK4)
% 6.99/1.52      | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1836,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.99/1.52      | ~ v1_funct_1(sK4)
% 6.99/1.52      | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_1652]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2846,plain,
% 6.99/1.52      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_2507,c_23,c_21,c_1836]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_18,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.99/1.52      inference(cnf_transformation,[],[f72]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_788,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_18]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1264,plain,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2506,plain,
% 6.99/1.52      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1264,c_1259]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_20,negated_conjecture,
% 6.99/1.52      ( v1_funct_1(sK5) ),
% 6.99/1.52      inference(cnf_transformation,[],[f70]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1647,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 6.99/1.52      | ~ v1_funct_1(sK5)
% 6.99/1.52      | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_794]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1827,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 6.99/1.52      | ~ v1_funct_1(sK5)
% 6.99/1.52      | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 6.99/1.52      inference(instantiation,[status(thm)],[c_1647]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2841,plain,
% 6.99/1.52      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_2506,c_20,c_18,c_1827]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_12,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f76]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_16,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f57]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_15,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f58]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_14,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f59]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_177,plain,
% 6.99/1.52      ( ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_12,c_16,c_15,c_14]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_178,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_177]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_775,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.99/1.52      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.99/1.52      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.99/1.52      | ~ v1_funct_1(X0_51)
% 6.99/1.52      | ~ v1_funct_1(X3_51)
% 6.99/1.52      | v1_xboole_0(X1_51)
% 6.99/1.52      | v1_xboole_0(X2_51)
% 6.99/1.52      | v1_xboole_0(X4_51)
% 6.99/1.52      | v1_xboole_0(X5_51)
% 6.99/1.52      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_178]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1277,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
% 6.99/1.52      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 6.99/1.52      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 6.99/1.52      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 6.99/1.52      | v1_funct_1(X2_51) != iProver_top
% 6.99/1.52      | v1_funct_1(X5_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X3_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_6720,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 6.99/1.52      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.99/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1_51) != iProver_top
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK1) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2841,c_1277]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_29,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f61]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_32,plain,
% 6.99/1.52      ( v1_xboole_0(sK1) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_26,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK3) ),
% 6.99/1.52      inference(cnf_transformation,[],[f64]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_35,plain,
% 6.99/1.52      ( v1_xboole_0(sK3) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_41,plain,
% 6.99/1.52      ( v1_funct_1(sK5) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_19,negated_conjecture,
% 6.99/1.52      ( v1_funct_2(sK5,sK3,sK1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f71]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_42,plain,
% 6.99/1.52      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_43,plain,
% 6.99/1.52      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_16904,plain,
% 6.99/1.52      ( v1_funct_1(X1_51) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 6.99/1.52      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_6720,c_32,c_35,c_41,c_42,c_43]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_16905,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 6.99/1.52      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_16904]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_16920,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 6.99/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(sK4) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2846,c_16905]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_28,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK2) ),
% 6.99/1.52      inference(cnf_transformation,[],[f62]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_33,plain,
% 6.99/1.52      ( v1_xboole_0(sK2) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_38,plain,
% 6.99/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_22,negated_conjecture,
% 6.99/1.52      ( v1_funct_2(sK4,sK2,sK1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f68]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_39,plain,
% 6.99/1.52      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_40,plain,
% 6.99/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17486,plain,
% 6.99/1.52      ( v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_16920,c_33,c_38,c_39,c_40]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17487,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_17486]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17497,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2450,c_17487]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1,plain,
% 6.99/1.52      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f43]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_230,plain,
% 6.99/1.52      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.99/1.52      inference(prop_impl,[status(thm)],[c_1]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_7,plain,
% 6.99/1.52      ( ~ r1_subset_1(X0,X1)
% 6.99/1.52      | r1_xboole_0(X0,X1)
% 6.99/1.52      | v1_xboole_0(X0)
% 6.99/1.52      | v1_xboole_0(X1) ),
% 6.99/1.52      inference(cnf_transformation,[],[f49]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_24,negated_conjecture,
% 6.99/1.52      ( r1_subset_1(sK2,sK3) ),
% 6.99/1.52      inference(cnf_transformation,[],[f66]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_444,plain,
% 6.99/1.52      ( r1_xboole_0(X0,X1)
% 6.99/1.52      | v1_xboole_0(X0)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | sK3 != X1
% 6.99/1.52      | sK2 != X0 ),
% 6.99/1.52      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_445,plain,
% 6.99/1.52      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 6.99/1.52      inference(unflattening,[status(thm)],[c_444]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_447,plain,
% 6.99/1.52      ( r1_xboole_0(sK2,sK3) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_445,c_28,c_26]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_502,plain,
% 6.99/1.52      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 6.99/1.52      inference(resolution_lifted,[status(thm)],[c_230,c_447]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_503,plain,
% 6.99/1.52      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.99/1.52      inference(unflattening,[status(thm)],[c_502]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_769,plain,
% 6.99/1.52      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_503]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9,plain,
% 6.99/1.52      ( v4_relat_1(X0,X1)
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.99/1.52      inference(cnf_transformation,[],[f52]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5,plain,
% 6.99/1.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f48]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_405,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ v1_relat_1(X0)
% 6.99/1.52      | k7_relat_1(X0,X1) = X0 ),
% 6.99/1.52      inference(resolution,[status(thm)],[c_9,c_5]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | v1_relat_1(X0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f51]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_409,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | k7_relat_1(X0,X1) = X0 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_405,c_9,c_8,c_5]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_774,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | k7_relat_1(X0_51,X1_51) = X0_51 ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_409]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1278,plain,
% 6.99/1.52      ( k7_relat_1(X0_51,X1_51) = X0_51
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10256,plain,
% 6.99/1.52      ( k7_relat_1(sK5,sK3) = sK5 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1264,c_1278]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_795,plain,
% 6.99/1.52      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | v1_relat_1(X0_51) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_8]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1258,plain,
% 6.99/1.52      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.99/1.52      | v1_relat_1(X0_51) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_795]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2226,plain,
% 6.99/1.52      ( v1_relat_1(sK5) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1264,c_1258]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4,plain,
% 6.99/1.52      ( ~ r1_xboole_0(X0,X1)
% 6.99/1.52      | ~ v1_relat_1(X2)
% 6.99/1.52      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 6.99/1.52      inference(cnf_transformation,[],[f47]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2,plain,
% 6.99/1.52      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f45]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_472,plain,
% 6.99/1.52      ( ~ v1_relat_1(X0)
% 6.99/1.52      | X1 != X2
% 6.99/1.52      | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
% 6.99/1.52      | k1_xboole_0 != X3 ),
% 6.99/1.52      inference(resolution_lifted,[status(thm)],[c_4,c_2]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_473,plain,
% 6.99/1.52      ( ~ v1_relat_1(X0)
% 6.99/1.52      | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(unflattening,[status(thm)],[c_472]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_772,plain,
% 6.99/1.52      ( ~ v1_relat_1(X0_51)
% 6.99/1.52      | k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_473]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1280,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0
% 6.99/1.52      | v1_relat_1(X0_51) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2379,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(sK5,X0_51),k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2226,c_1280]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10801,plain,
% 6.99/1.52      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_10256,c_2379]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17498,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(light_normalisation,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_17497,c_769,c_10801]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_792,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.99/1.52      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.99/1.52      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.99/1.52      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
% 6.99/1.52      | ~ v1_funct_1(X0_51)
% 6.99/1.52      | ~ v1_funct_1(X3_51)
% 6.99/1.52      | v1_xboole_0(X1_51)
% 6.99/1.52      | v1_xboole_0(X2_51)
% 6.99/1.52      | v1_xboole_0(X4_51)
% 6.99/1.52      | v1_xboole_0(X5_51) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_14]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1261,plain,
% 6.99/1.52      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 6.99/1.52      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 6.99/1.52      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
% 6.99/1.52      | v1_funct_1(X0_51) != iProver_top
% 6.99/1.52      | v1_funct_1(X3_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X5_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_792]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2605,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 6.99/1.52      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 6.99/1.52      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 6.99/1.52      | v1_funct_1(X5_51) != iProver_top
% 6.99/1.52      | v1_funct_1(X4_51) != iProver_top
% 6.99/1.52      | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X3_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1261,c_1259]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_790,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.99/1.52      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.99/1.52      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.99/1.52      | ~ v1_funct_1(X0_51)
% 6.99/1.52      | ~ v1_funct_1(X3_51)
% 6.99/1.52      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
% 6.99/1.52      | v1_xboole_0(X1_51)
% 6.99/1.52      | v1_xboole_0(X2_51)
% 6.99/1.52      | v1_xboole_0(X4_51)
% 6.99/1.52      | v1_xboole_0(X5_51) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_16]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1263,plain,
% 6.99/1.52      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 6.99/1.52      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 6.99/1.52      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 6.99/1.52      | v1_funct_1(X0_51) != iProver_top
% 6.99/1.52      | v1_funct_1(X3_51) != iProver_top
% 6.99/1.52      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
% 6.99/1.52      | v1_xboole_0(X5_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5421,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 6.99/1.52      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 6.99/1.52      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 6.99/1.52      | v1_funct_1(X5_51) != iProver_top
% 6.99/1.52      | v1_funct_1(X4_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X3_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(forward_subsumption_resolution,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_2605,c_1263]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5425,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 6.99/1.52      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 6.99/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(X2_51) != iProver_top
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK1) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1264,c_5421]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5586,plain,
% 6.99/1.52      ( v1_funct_1(X2_51) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 6.99/1.52      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_5425,c_32,c_35,c_41,c_42]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5587,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 6.99/1.52      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(X2_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_5586]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5601,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 6.99/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(sK4) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1267,c_5587]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5812,plain,
% 6.99/1.52      ( v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_5601,c_33,c_38,c_39]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5813,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_5812]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5822,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1270,c_5813]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_30,negated_conjecture,
% 6.99/1.52      ( ~ v1_xboole_0(sK0) ),
% 6.99/1.52      inference(cnf_transformation,[],[f60]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_31,plain,
% 6.99/1.52      ( v1_xboole_0(sK0) != iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_27,negated_conjecture,
% 6.99/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f63]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_34,plain,
% 6.99/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5879,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_5822,c_31,c_34]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17499,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_17498,c_2450,c_5879]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10257,plain,
% 6.99/1.52      ( k7_relat_1(sK4,sK2) = sK4 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1267,c_1278]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2227,plain,
% 6.99/1.52      ( v1_relat_1(sK4) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_1267,c_1258]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2388,plain,
% 6.99/1.52      ( k7_relat_1(k7_relat_1(sK4,X0_51),k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2227,c_1280]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10804,plain,
% 6.99/1.52      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_10257,c_2388]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17500,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | k1_xboole_0 != k1_xboole_0
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(light_normalisation,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_17499,c_769,c_10804]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17501,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(equality_resolution_simp,[status(thm)],[c_17500]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_13,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.99/1.52      inference(cnf_transformation,[],[f77]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_170,plain,
% 6.99/1.52      ( ~ v1_funct_1(X3)
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_13,c_16,c_15,c_14]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_171,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 6.99/1.52      | ~ v1_funct_2(X3,X4,X2)
% 6.99/1.52      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.99/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.99/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.99/1.52      | ~ v1_funct_1(X0)
% 6.99/1.52      | ~ v1_funct_1(X3)
% 6.99/1.52      | v1_xboole_0(X1)
% 6.99/1.52      | v1_xboole_0(X2)
% 6.99/1.52      | v1_xboole_0(X4)
% 6.99/1.52      | v1_xboole_0(X5)
% 6.99/1.52      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_170]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_776,plain,
% 6.99/1.52      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.99/1.52      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.99/1.52      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.99/1.52      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.99/1.52      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.99/1.52      | ~ v1_funct_1(X0_51)
% 6.99/1.52      | ~ v1_funct_1(X3_51)
% 6.99/1.52      | v1_xboole_0(X1_51)
% 6.99/1.52      | v1_xboole_0(X2_51)
% 6.99/1.52      | v1_xboole_0(X4_51)
% 6.99/1.52      | v1_xboole_0(X5_51)
% 6.99/1.52      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_171]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_1276,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
% 6.99/1.52      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 6.99/1.52      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 6.99/1.52      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.99/1.52      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 6.99/1.52      | v1_funct_1(X2_51) != iProver_top
% 6.99/1.52      | v1_funct_1(X5_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X3_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X1_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X4_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_4693,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 6.99/1.52      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.99/1.52      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1_51) != iProver_top
% 6.99/1.52      | v1_funct_1(sK5) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK1) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK3) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2841,c_1276]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8548,plain,
% 6.99/1.52      ( v1_funct_1(X1_51) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 6.99/1.52      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_4693,c_32,c_35,c_41,c_42,c_43]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8549,plain,
% 6.99/1.52      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 6.99/1.52      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 6.99/1.52      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(X1_51) != iProver_top
% 6.99/1.52      | v1_xboole_0(X2_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_8548]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_8564,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 6.99/1.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.99/1.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_funct_1(sK4) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | v1_xboole_0(sK2) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2846,c_8549]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9006,plain,
% 6.99/1.52      ( v1_xboole_0(X0_51) = iProver_top
% 6.99/1.52      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_8564,c_33,c_38,c_39,c_40]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9007,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.99/1.52      | v1_xboole_0(X0_51) = iProver_top ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_9006]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9017,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(superposition,[status(thm)],[c_2450,c_9007]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9018,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_9017,c_769]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9019,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_9018,c_2450,c_5879]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9020,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 6.99/1.52      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.99/1.52      | v1_xboole_0(sK0) = iProver_top ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_9019,c_769]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_9021,plain,
% 6.99/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 6.99/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 6.99/1.52      | v1_xboole_0(sK0)
% 6.99/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 6.99/1.52      inference(predicate_to_equality_rev,[status(thm)],[c_9020]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10249,plain,
% 6.99/1.52      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 6.99/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 6.99/1.52      inference(global_propositional_subsumption,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_9020,c_30,c_27,c_25,c_9021]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_10250,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 6.99/1.52      inference(renaming,[status(thm)],[c_10249]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11843,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.99/1.52      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_10801,c_10250]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_17,negated_conjecture,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.99/1.52      inference(cnf_transformation,[],[f73]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_789,negated_conjecture,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.99/1.52      inference(subtyping,[status(esa)],[c_17]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2740,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_2450,c_789]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2741,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 6.99/1.52      inference(light_normalisation,[status(thm)],[c_2740,c_769]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_2944,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_2741,c_2841,c_2846]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5883,plain,
% 6.99/1.52      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_5879,c_2944]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_5884,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_5883,c_5879]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11844,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.99/1.52      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 6.99/1.52      inference(demodulation,[status(thm)],[c_10801,c_5884]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_11854,plain,
% 6.99/1.52      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.99/1.52      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 6.99/1.52      inference(backward_subsumption_resolution,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_11843,c_11844]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(c_36,plain,
% 6.99/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.99/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.99/1.52  
% 6.99/1.52  cnf(contradiction,plain,
% 6.99/1.52      ( $false ),
% 6.99/1.52      inference(minisat,
% 6.99/1.52                [status(thm)],
% 6.99/1.52                [c_17501,c_11854,c_10804,c_36,c_34,c_31]) ).
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 6.99/1.52  
% 6.99/1.52  ------                               Statistics
% 6.99/1.52  
% 6.99/1.52  ------ General
% 6.99/1.52  
% 6.99/1.52  abstr_ref_over_cycles:                  0
% 6.99/1.52  abstr_ref_under_cycles:                 0
% 6.99/1.52  gc_basic_clause_elim:                   0
% 6.99/1.52  forced_gc_time:                         0
% 6.99/1.52  parsing_time:                           0.013
% 6.99/1.52  unif_index_cands_time:                  0.
% 6.99/1.52  unif_index_add_time:                    0.
% 6.99/1.52  orderings_time:                         0.
% 6.99/1.52  out_proof_time:                         0.017
% 6.99/1.52  total_time:                             0.953
% 6.99/1.52  num_of_symbols:                         56
% 6.99/1.52  num_of_terms:                           40409
% 6.99/1.52  
% 6.99/1.52  ------ Preprocessing
% 6.99/1.52  
% 6.99/1.52  num_of_splits:                          0
% 6.99/1.52  num_of_split_atoms:                     0
% 6.99/1.52  num_of_reused_defs:                     0
% 6.99/1.52  num_eq_ax_congr_red:                    9
% 6.99/1.52  num_of_sem_filtered_clauses:            1
% 6.99/1.52  num_of_subtypes:                        2
% 6.99/1.52  monotx_restored_types:                  0
% 6.99/1.52  sat_num_of_epr_types:                   0
% 6.99/1.52  sat_num_of_non_cyclic_types:            0
% 6.99/1.52  sat_guarded_non_collapsed_types:        1
% 6.99/1.52  num_pure_diseq_elim:                    0
% 6.99/1.52  simp_replaced_by:                       0
% 6.99/1.52  res_preprocessed:                       146
% 6.99/1.52  prep_upred:                             0
% 6.99/1.52  prep_unflattend:                        11
% 6.99/1.52  smt_new_axioms:                         0
% 6.99/1.52  pred_elim_cands:                        5
% 6.99/1.52  pred_elim:                              3
% 6.99/1.52  pred_elim_cl:                           3
% 6.99/1.52  pred_elim_cycles:                       6
% 6.99/1.52  merged_defs:                            2
% 6.99/1.52  merged_defs_ncl:                        0
% 6.99/1.52  bin_hyper_res:                          2
% 6.99/1.52  prep_cycles:                            4
% 6.99/1.52  pred_elim_time:                         0.004
% 6.99/1.52  splitting_time:                         0.
% 6.99/1.52  sem_filter_time:                        0.
% 6.99/1.52  monotx_time:                            0.
% 6.99/1.52  subtype_inf_time:                       0.001
% 6.99/1.52  
% 6.99/1.52  ------ Problem properties
% 6.99/1.52  
% 6.99/1.52  clauses:                                28
% 6.99/1.52  conjectures:                            13
% 6.99/1.52  epr:                                    8
% 6.99/1.52  horn:                                   22
% 6.99/1.52  ground:                                 14
% 6.99/1.52  unary:                                  14
% 6.99/1.52  binary:                                 5
% 6.99/1.52  lits:                                   117
% 6.99/1.52  lits_eq:                                18
% 6.99/1.52  fd_pure:                                0
% 6.99/1.52  fd_pseudo:                              0
% 6.99/1.52  fd_cond:                                0
% 6.99/1.52  fd_pseudo_cond:                         0
% 6.99/1.52  ac_symbols:                             0
% 6.99/1.52  
% 6.99/1.52  ------ Propositional Solver
% 6.99/1.52  
% 6.99/1.52  prop_solver_calls:                      29
% 6.99/1.52  prop_fast_solver_calls:                 2937
% 6.99/1.52  smt_solver_calls:                       0
% 6.99/1.52  smt_fast_solver_calls:                  0
% 6.99/1.52  prop_num_of_clauses:                    7416
% 6.99/1.52  prop_preprocess_simplified:             15361
% 6.99/1.52  prop_fo_subsumed:                       205
% 6.99/1.52  prop_solver_time:                       0.
% 6.99/1.52  smt_solver_time:                        0.
% 6.99/1.52  smt_fast_solver_time:                   0.
% 6.99/1.52  prop_fast_solver_time:                  0.
% 6.99/1.52  prop_unsat_core_time:                   0.001
% 6.99/1.52  
% 6.99/1.52  ------ QBF
% 6.99/1.52  
% 6.99/1.52  qbf_q_res:                              0
% 6.99/1.52  qbf_num_tautologies:                    0
% 6.99/1.52  qbf_prep_cycles:                        0
% 6.99/1.52  
% 6.99/1.52  ------ BMC1
% 6.99/1.52  
% 6.99/1.52  bmc1_current_bound:                     -1
% 6.99/1.52  bmc1_last_solved_bound:                 -1
% 6.99/1.52  bmc1_unsat_core_size:                   -1
% 6.99/1.52  bmc1_unsat_core_parents_size:           -1
% 6.99/1.52  bmc1_merge_next_fun:                    0
% 6.99/1.52  bmc1_unsat_core_clauses_time:           0.
% 6.99/1.52  
% 6.99/1.52  ------ Instantiation
% 6.99/1.52  
% 6.99/1.52  inst_num_of_clauses:                    1731
% 6.99/1.52  inst_num_in_passive:                    975
% 6.99/1.52  inst_num_in_active:                     622
% 6.99/1.52  inst_num_in_unprocessed:                134
% 6.99/1.52  inst_num_of_loops:                      670
% 6.99/1.52  inst_num_of_learning_restarts:          0
% 6.99/1.52  inst_num_moves_active_passive:          45
% 6.99/1.52  inst_lit_activity:                      0
% 6.99/1.52  inst_lit_activity_moves:                1
% 6.99/1.52  inst_num_tautologies:                   0
% 6.99/1.52  inst_num_prop_implied:                  0
% 6.99/1.52  inst_num_existing_simplified:           0
% 6.99/1.52  inst_num_eq_res_simplified:             0
% 6.99/1.52  inst_num_child_elim:                    0
% 6.99/1.52  inst_num_of_dismatching_blockings:      55
% 6.99/1.52  inst_num_of_non_proper_insts:           1037
% 6.99/1.52  inst_num_of_duplicates:                 0
% 6.99/1.52  inst_inst_num_from_inst_to_res:         0
% 6.99/1.52  inst_dismatching_checking_time:         0.
% 6.99/1.52  
% 6.99/1.52  ------ Resolution
% 6.99/1.52  
% 6.99/1.52  res_num_of_clauses:                     0
% 6.99/1.52  res_num_in_passive:                     0
% 6.99/1.52  res_num_in_active:                      0
% 6.99/1.52  res_num_of_loops:                       150
% 6.99/1.52  res_forward_subset_subsumed:            45
% 6.99/1.52  res_backward_subset_subsumed:           0
% 6.99/1.52  res_forward_subsumed:                   0
% 6.99/1.52  res_backward_subsumed:                  0
% 6.99/1.52  res_forward_subsumption_resolution:     0
% 6.99/1.52  res_backward_subsumption_resolution:    0
% 6.99/1.52  res_clause_to_clause_subsumption:       2448
% 6.99/1.52  res_orphan_elimination:                 0
% 6.99/1.52  res_tautology_del:                      27
% 6.99/1.52  res_num_eq_res_simplified:              0
% 6.99/1.52  res_num_sel_changes:                    0
% 6.99/1.52  res_moves_from_active_to_pass:          0
% 6.99/1.52  
% 6.99/1.52  ------ Superposition
% 6.99/1.52  
% 6.99/1.52  sup_time_total:                         0.
% 6.99/1.52  sup_time_generating:                    0.
% 6.99/1.52  sup_time_sim_full:                      0.
% 6.99/1.52  sup_time_sim_immed:                     0.
% 6.99/1.52  
% 6.99/1.52  sup_num_of_clauses:                     230
% 6.99/1.52  sup_num_in_active:                      128
% 6.99/1.52  sup_num_in_passive:                     102
% 6.99/1.52  sup_num_of_loops:                       132
% 6.99/1.52  sup_fw_superposition:                   211
% 6.99/1.52  sup_bw_superposition:                   34
% 6.99/1.52  sup_immediate_simplified:               112
% 6.99/1.52  sup_given_eliminated:                   0
% 6.99/1.52  comparisons_done:                       0
% 6.99/1.52  comparisons_avoided:                    0
% 6.99/1.52  
% 6.99/1.52  ------ Simplifications
% 6.99/1.52  
% 6.99/1.52  
% 6.99/1.52  sim_fw_subset_subsumed:                 0
% 6.99/1.52  sim_bw_subset_subsumed:                 1
% 6.99/1.52  sim_fw_subsumed:                        12
% 6.99/1.52  sim_bw_subsumed:                        8
% 6.99/1.52  sim_fw_subsumption_res:                 1
% 6.99/1.52  sim_bw_subsumption_res:                 1
% 6.99/1.52  sim_tautology_del:                      0
% 6.99/1.52  sim_eq_tautology_del:                   6
% 6.99/1.52  sim_eq_res_simp:                        4
% 6.99/1.52  sim_fw_demodulated:                     63
% 6.99/1.52  sim_bw_demodulated:                     5
% 6.99/1.52  sim_light_normalised:                   45
% 6.99/1.52  sim_joinable_taut:                      0
% 6.99/1.52  sim_joinable_simp:                      0
% 6.99/1.52  sim_ac_normalised:                      0
% 6.99/1.52  sim_smt_subsumption:                    0
% 6.99/1.52  
%------------------------------------------------------------------------------
