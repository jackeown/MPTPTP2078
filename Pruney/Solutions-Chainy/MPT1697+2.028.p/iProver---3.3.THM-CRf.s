%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:27 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  255 (3020 expanded)
%              Number of clauses        :  167 ( 819 expanded)
%              Number of leaves         :   23 (1024 expanded)
%              Depth                    :   28
%              Number of atoms          : 1297 (32094 expanded)
%              Number of equality atoms :  494 (7311 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f44,f55,f54,f53,f52,f51,f50])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f77])).

fof(f17,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f90,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f93,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f95,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1040,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1705,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1046,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1700,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_4922,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1700])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2231,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2518,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_5011,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4922,c_28,c_26,c_2518])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1033,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1712,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1058,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1689,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1058])).

cnf(c_2488,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1712,c_1689])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1037,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1708,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_4923,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1700])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2236,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_2523,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_5017,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4923,c_31,c_29,c_2523])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f79])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_211,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_24,c_23,c_22])).

cnf(c_212,plain,
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
    inference(renaming,[status(thm)],[c_211])).

cnf(c_1026,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_212])).

cnf(c_1719,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
    | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1057,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1690,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_1957,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
    | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1719,c_1690])).

cnf(c_12925,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_1957])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_40,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_41,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_46,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_47,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23139,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12925,c_40,c_41,c_46,c_47,c_48])).

cnf(c_23140,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_23139])).

cnf(c_23157,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_23140])).

cnf(c_32,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1034,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1711,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1049,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_xboole_0(X0_53,X1_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1697,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X0_53,X1_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_3857,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1697])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_45,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2161,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_2162,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_3860,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3857,c_41,c_43,c_45,c_2162])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_396,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_13,c_17])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_17,c_13,c_12])).

cnf(c_401,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_440,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_14,c_401])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_17,c_14,c_13,c_12])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1025,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_445])).

cnf(c_1720,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1025])).

cnf(c_5739,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1720])).

cnf(c_2210,plain,
    ( ~ v1_funct_2(sK4,X0_53,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_2515,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2210])).

cnf(c_6465,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5739,c_37,c_31,c_30,c_29,c_2515])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1052,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_53),X1_53)
    | ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1694,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_53),X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1052])).

cnf(c_6468,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(sK2,X0_53) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6465,c_1694])).

cnf(c_1047,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2107,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_2108,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_6568,plain,
    ( r1_xboole_0(sK2,X0_53) != iProver_top
    | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6468,c_48,c_2108])).

cnf(c_6569,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(sK2,X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_6568])).

cnf(c_6576,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3860,c_6569])).

cnf(c_1699,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_2913,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_1699])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1055,plain,
    ( ~ v1_relat_1(X0_53)
    | k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1692,plain,
    ( k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1055])).

cnf(c_3109,plain,
    ( k3_xboole_0(k7_relat_1(sK4,X0_53),k7_relat_1(sK4,X1_53)) = k7_relat_1(sK4,k3_xboole_0(X0_53,X1_53)) ),
    inference(superposition,[status(thm)],[c_2913,c_1692])).

cnf(c_6723,plain,
    ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k3_xboole_0(k7_relat_1(sK4,X0_53),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6576,c_3109])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1059,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_6725,plain,
    ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6723,c_1059])).

cnf(c_23182,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_23157,c_2488,c_6725])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23344,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_23182,c_42,c_43,c_44])).

cnf(c_23345,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_23344])).

cnf(c_23355,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5011,c_23345])).

cnf(c_11,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1048,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_subset_1(X1_53,X0_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1698,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_subset_1(X1_53,X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1048])).

cnf(c_4598,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1698])).

cnf(c_2158,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ r1_subset_1(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_2159,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2158])).

cnf(c_5086,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4598,c_41,c_43,c_45,c_2159])).

cnf(c_5092,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5086,c_1697])).

cnf(c_2376,plain,
    ( ~ r1_subset_1(sK3,sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1049])).

cnf(c_2378,plain,
    ( r1_subset_1(sK3,sK2) != iProver_top
    | r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2376])).

cnf(c_5167,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5092,c_41,c_43,c_45,c_2159,c_2378])).

cnf(c_5738,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1720])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2205,plain,
    ( ~ v1_funct_2(sK5,X0_53,X1_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_53)
    | k1_relat_1(sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_2512,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2205])).

cnf(c_6218,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5738,c_37,c_28,c_27,c_26,c_2512])).

cnf(c_6221,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_xboole_0(sK3,X0_53) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6218,c_1694])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_2105,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_6487,plain,
    ( r1_xboole_0(sK3,X0_53) != iProver_top
    | k7_relat_1(sK5,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6221,c_51,c_2105])).

cnf(c_6488,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_xboole_0(sK3,X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_6487])).

cnf(c_6495,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5167,c_6488])).

cnf(c_2912,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1705,c_1699])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1056,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1691,plain,
    ( k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_3100,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0_53),X1_53) = k7_relat_1(sK5,k3_xboole_0(X0_53,X1_53)) ),
    inference(superposition,[status(thm)],[c_2912,c_1691])).

cnf(c_6926,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k7_relat_1(k1_xboole_0,X0_53) ),
    inference(superposition,[status(thm)],[c_6495,c_3100])).

cnf(c_5,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1054,plain,
    ( k7_relat_1(k1_xboole_0,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_6932,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6926,c_1054])).

cnf(c_23356,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_23355,c_6932])).

cnf(c_23357,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23356])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f100])).

cnf(c_204,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_24,c_23,c_22])).

cnf(c_205,plain,
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
    inference(renaming,[status(thm)],[c_204])).

cnf(c_1027,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_205])).

cnf(c_1718,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
    | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1027])).

cnf(c_1929,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
    | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1718,c_1690])).

cnf(c_11319,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5017,c_1929])).

cnf(c_15581,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11319,c_40,c_41,c_46,c_47,c_48])).

cnf(c_15582,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_15581])).

cnf(c_15599,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_15582])).

cnf(c_15624,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15599,c_2488,c_6725])).

cnf(c_17319,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15624,c_42,c_43,c_44])).

cnf(c_17320,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_17319])).

cnf(c_17330,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5011,c_17320])).

cnf(c_17331,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17330,c_6932])).

cnf(c_17332,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17331])).

cnf(c_25,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1041,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_2680,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2488,c_1041])).

cnf(c_5015,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_5011,c_2680])).

cnf(c_5081,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_5015,c_5017])).

cnf(c_7005,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6725,c_5081])).

cnf(c_11047,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7005,c_6932])).

cnf(c_11048,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_11047])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23357,c_17332,c_11048,c_51,c_50,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.70/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.70/1.50  
% 7.70/1.50  ------  iProver source info
% 7.70/1.50  
% 7.70/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.70/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.70/1.50  git: non_committed_changes: false
% 7.70/1.50  git: last_make_outside_of_git: false
% 7.70/1.50  
% 7.70/1.50  ------ 
% 7.70/1.50  ------ Parsing...
% 7.70/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.70/1.50  
% 7.70/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.50  ------ Proving...
% 7.70/1.50  ------ Problem Properties 
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  clauses                                 35
% 7.70/1.50  conjectures                             14
% 7.70/1.50  EPR                                     12
% 7.70/1.50  Horn                                    25
% 7.70/1.50  unary                                   15
% 7.70/1.50  binary                                  4
% 7.70/1.50  lits                                    142
% 7.70/1.50  lits eq                                 19
% 7.70/1.50  fd_pure                                 0
% 7.70/1.50  fd_pseudo                               0
% 7.70/1.50  fd_cond                                 0
% 7.70/1.50  fd_pseudo_cond                          1
% 7.70/1.50  AC symbols                              0
% 7.70/1.50  
% 7.70/1.50  ------ Input Options Time Limit: Unbounded
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ 
% 7.70/1.50  Current options:
% 7.70/1.50  ------ 
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  ------ Proving...
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  % SZS status Theorem for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  fof(f18,conjecture,(
% 7.70/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f19,negated_conjecture,(
% 7.70/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.70/1.50    inference(negated_conjecture,[],[f18])).
% 7.70/1.50  
% 7.70/1.50  fof(f43,plain,(
% 7.70/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f19])).
% 7.70/1.50  
% 7.70/1.50  fof(f44,plain,(
% 7.70/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.70/1.50    inference(flattening,[],[f43])).
% 7.70/1.50  
% 7.70/1.50  fof(f55,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f54,plain,(
% 7.70/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f53,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f52,plain,(
% 7.70/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f51,plain,(
% 7.70/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f50,plain,(
% 7.70/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.70/1.50    introduced(choice_axiom,[])).
% 7.70/1.50  
% 7.70/1.50  fof(f56,plain,(
% 7.70/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.70/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f44,f55,f54,f53,f52,f51,f50])).
% 7.70/1.50  
% 7.70/1.50  fof(f94,plain,(
% 7.70/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f15,axiom,(
% 7.70/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f37,plain,(
% 7.70/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.70/1.50    inference(ennf_transformation,[],[f15])).
% 7.70/1.50  
% 7.70/1.50  fof(f38,plain,(
% 7.70/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.70/1.50    inference(flattening,[],[f37])).
% 7.70/1.50  
% 7.70/1.50  fof(f75,plain,(
% 7.70/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f38])).
% 7.70/1.50  
% 7.70/1.50  fof(f92,plain,(
% 7.70/1.50    v1_funct_1(sK5)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f87,plain,(
% 7.70/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f2,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f21,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.70/1.50    inference(ennf_transformation,[],[f2])).
% 7.70/1.50  
% 7.70/1.50  fof(f58,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.70/1.50    inference(cnf_transformation,[],[f21])).
% 7.70/1.50  
% 7.70/1.50  fof(f91,plain,(
% 7.70/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f89,plain,(
% 7.70/1.50    v1_funct_1(sK4)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f16,axiom,(
% 7.70/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f39,plain,(
% 7.70/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f16])).
% 7.70/1.50  
% 7.70/1.50  fof(f40,plain,(
% 7.70/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.50    inference(flattening,[],[f39])).
% 7.70/1.50  
% 7.70/1.50  fof(f48,plain,(
% 7.70/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.50    inference(nnf_transformation,[],[f40])).
% 7.70/1.50  
% 7.70/1.50  fof(f49,plain,(
% 7.70/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.50    inference(flattening,[],[f48])).
% 7.70/1.50  
% 7.70/1.50  fof(f77,plain,(
% 7.70/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f49])).
% 7.70/1.50  
% 7.70/1.50  fof(f99,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(equality_resolution,[],[f77])).
% 7.70/1.50  
% 7.70/1.50  fof(f17,axiom,(
% 7.70/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f41,plain,(
% 7.70/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.70/1.50    inference(ennf_transformation,[],[f17])).
% 7.70/1.50  
% 7.70/1.50  fof(f42,plain,(
% 7.70/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.50    inference(flattening,[],[f41])).
% 7.70/1.50  
% 7.70/1.50  fof(f79,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f42])).
% 7.70/1.50  
% 7.70/1.50  fof(f80,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f42])).
% 7.70/1.50  
% 7.70/1.50  fof(f81,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f42])).
% 7.70/1.50  
% 7.70/1.50  fof(f3,axiom,(
% 7.70/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f22,plain,(
% 7.70/1.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.70/1.50    inference(ennf_transformation,[],[f3])).
% 7.70/1.50  
% 7.70/1.50  fof(f59,plain,(
% 7.70/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f22])).
% 7.70/1.50  
% 7.70/1.50  fof(f83,plain,(
% 7.70/1.50    ~v1_xboole_0(sK1)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f84,plain,(
% 7.70/1.50    ~v1_xboole_0(sK2)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f90,plain,(
% 7.70/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f88,plain,(
% 7.70/1.50    r1_subset_1(sK2,sK3)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f9,axiom,(
% 7.70/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f27,plain,(
% 7.70/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.70/1.50    inference(ennf_transformation,[],[f9])).
% 7.70/1.50  
% 7.70/1.50  fof(f28,plain,(
% 7.70/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.50    inference(flattening,[],[f27])).
% 7.70/1.50  
% 7.70/1.50  fof(f46,plain,(
% 7.70/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.50    inference(nnf_transformation,[],[f28])).
% 7.70/1.50  
% 7.70/1.50  fof(f66,plain,(
% 7.70/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f46])).
% 7.70/1.50  
% 7.70/1.50  fof(f86,plain,(
% 7.70/1.50    ~v1_xboole_0(sK3)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f13,axiom,(
% 7.70/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f33,plain,(
% 7.70/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.70/1.50    inference(ennf_transformation,[],[f13])).
% 7.70/1.50  
% 7.70/1.50  fof(f34,plain,(
% 7.70/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.70/1.50    inference(flattening,[],[f33])).
% 7.70/1.50  
% 7.70/1.50  fof(f72,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f34])).
% 7.70/1.50  
% 7.70/1.50  fof(f12,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f20,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.70/1.50    inference(pure_predicate_removal,[],[f12])).
% 7.70/1.50  
% 7.70/1.50  fof(f32,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.50    inference(ennf_transformation,[],[f20])).
% 7.70/1.50  
% 7.70/1.50  fof(f70,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.50    inference(cnf_transformation,[],[f32])).
% 7.70/1.50  
% 7.70/1.50  fof(f14,axiom,(
% 7.70/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f35,plain,(
% 7.70/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.70/1.50    inference(ennf_transformation,[],[f14])).
% 7.70/1.50  
% 7.70/1.50  fof(f36,plain,(
% 7.70/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.70/1.50    inference(flattening,[],[f35])).
% 7.70/1.50  
% 7.70/1.50  fof(f47,plain,(
% 7.70/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.70/1.50    inference(nnf_transformation,[],[f36])).
% 7.70/1.50  
% 7.70/1.50  fof(f73,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f47])).
% 7.70/1.50  
% 7.70/1.50  fof(f11,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f31,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.50    inference(ennf_transformation,[],[f11])).
% 7.70/1.50  
% 7.70/1.50  fof(f69,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.50    inference(cnf_transformation,[],[f31])).
% 7.70/1.50  
% 7.70/1.50  fof(f8,axiom,(
% 7.70/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f26,plain,(
% 7.70/1.50    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.70/1.50    inference(ennf_transformation,[],[f8])).
% 7.70/1.50  
% 7.70/1.50  fof(f45,plain,(
% 7.70/1.50    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.70/1.50    inference(nnf_transformation,[],[f26])).
% 7.70/1.50  
% 7.70/1.50  fof(f65,plain,(
% 7.70/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f45])).
% 7.70/1.50  
% 7.70/1.50  fof(f5,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f24,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.70/1.50    inference(ennf_transformation,[],[f5])).
% 7.70/1.50  
% 7.70/1.50  fof(f61,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f24])).
% 7.70/1.50  
% 7.70/1.50  fof(f1,axiom,(
% 7.70/1.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f57,plain,(
% 7.70/1.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f1])).
% 7.70/1.50  
% 7.70/1.50  fof(f85,plain,(
% 7.70/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f10,axiom,(
% 7.70/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f29,plain,(
% 7.70/1.50    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.70/1.50    inference(ennf_transformation,[],[f10])).
% 7.70/1.50  
% 7.70/1.50  fof(f30,plain,(
% 7.70/1.50    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.50    inference(flattening,[],[f29])).
% 7.70/1.50  
% 7.70/1.50  fof(f68,plain,(
% 7.70/1.50    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f30])).
% 7.70/1.50  
% 7.70/1.50  fof(f93,plain,(
% 7.70/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  fof(f4,axiom,(
% 7.70/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f23,plain,(
% 7.70/1.50    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.70/1.50    inference(ennf_transformation,[],[f4])).
% 7.70/1.50  
% 7.70/1.50  fof(f60,plain,(
% 7.70/1.50    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f23])).
% 7.70/1.50  
% 7.70/1.50  fof(f6,axiom,(
% 7.70/1.50    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 7.70/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.70/1.50  
% 7.70/1.50  fof(f62,plain,(
% 7.70/1.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f6])).
% 7.70/1.50  
% 7.70/1.50  fof(f76,plain,(
% 7.70/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(cnf_transformation,[],[f49])).
% 7.70/1.50  
% 7.70/1.50  fof(f100,plain,(
% 7.70/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.50    inference(equality_resolution,[],[f76])).
% 7.70/1.50  
% 7.70/1.50  fof(f95,plain,(
% 7.70/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.70/1.50    inference(cnf_transformation,[],[f56])).
% 7.70/1.50  
% 7.70/1.50  cnf(c_26,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.70/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1040,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_26]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1705,plain,
% 7.70/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_18,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.70/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1046,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.70/1.50      | ~ v1_funct_1(X0_53)
% 7.70/1.50      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_18]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1700,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.70/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.70/1.50      | v1_funct_1(X2_53) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1046]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_4922,plain,
% 7.70/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1705,c_1700]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_28,negated_conjecture,
% 7.70/1.50      ( v1_funct_1(sK5) ),
% 7.70/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2231,plain,
% 7.70/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.70/1.50      | ~ v1_funct_1(sK5)
% 7.70/1.50      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1046]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2518,plain,
% 7.70/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.70/1.50      | ~ v1_funct_1(sK5)
% 7.70/1.50      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_2231]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5011,plain,
% 7.70/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_4922,c_28,c_26,c_2518]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_33,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1033,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_33]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1712,plain,
% 7.70/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.70/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.70/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1058,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.70/1.50      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1689,plain,
% 7.70/1.50      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.70/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1058]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2488,plain,
% 7.70/1.50      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1712,c_1689]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_29,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.70/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1037,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_29]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1708,plain,
% 7.70/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_4923,plain,
% 7.70/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.70/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1708,c_1700]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_31,negated_conjecture,
% 7.70/1.50      ( v1_funct_1(sK4) ),
% 7.70/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2236,plain,
% 7.70/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.70/1.50      | ~ v1_funct_1(sK4)
% 7.70/1.50      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1046]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2523,plain,
% 7.70/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.70/1.50      | ~ v1_funct_1(sK4)
% 7.70/1.50      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_2236]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5017,plain,
% 7.70/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_4923,c_31,c_29,c_2523]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_20,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_24,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_22,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_211,plain,
% 7.70/1.50      ( ~ v1_funct_1(X3)
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_20,c_24,c_23,c_22]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_212,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | v1_xboole_0(X1)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_211]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1026,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.70/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.70/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.70/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.70/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.70/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.70/1.50      | ~ v1_funct_1(X0_53)
% 7.70/1.50      | ~ v1_funct_1(X3_53)
% 7.70/1.50      | v1_xboole_0(X2_53)
% 7.70/1.50      | v1_xboole_0(X1_53)
% 7.70/1.50      | v1_xboole_0(X4_53)
% 7.70/1.50      | v1_xboole_0(X5_53)
% 7.70/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_212]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1719,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.70/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.70/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.70/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.70/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.70/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.70/1.50      | ~ v1_xboole_0(X1)
% 7.70/1.50      | v1_xboole_0(X0) ),
% 7.70/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1057,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.70/1.50      | ~ v1_xboole_0(X1_53)
% 7.70/1.50      | v1_xboole_0(X0_53) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1690,plain,
% 7.70/1.50      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1957,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
% 7.70/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.70/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.70/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.70/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.70/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X4_53) = iProver_top ),
% 7.70/1.50      inference(forward_subsumption_resolution,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_1719,c_1690]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_12925,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.70/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.70/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.70/1.50      | v1_funct_1(sK4) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_5017,c_1957]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_37,negated_conjecture,
% 7.70/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_40,plain,
% 7.70/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_36,negated_conjecture,
% 7.70/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.70/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_41,plain,
% 7.70/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_46,plain,
% 7.70/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_30,negated_conjecture,
% 7.70/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_47,plain,
% 7.70/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_48,plain,
% 7.70/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23139,plain,
% 7.70/1.50      ( v1_funct_1(X1_53) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.70/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.70/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_12925,c_40,c_41,c_46,c_47,c_48]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23140,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.70/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_23139]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23157,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_2488,c_23140]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_32,negated_conjecture,
% 7.70/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.70/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1034,negated_conjecture,
% 7.70/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_32]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1711,plain,
% 7.70/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_10,plain,
% 7.70/1.50      ( ~ r1_subset_1(X0,X1)
% 7.70/1.50      | r1_xboole_0(X0,X1)
% 7.70/1.50      | v1_xboole_0(X0)
% 7.70/1.50      | v1_xboole_0(X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1049,plain,
% 7.70/1.50      ( ~ r1_subset_1(X0_53,X1_53)
% 7.70/1.50      | r1_xboole_0(X0_53,X1_53)
% 7.70/1.50      | v1_xboole_0(X1_53)
% 7.70/1.50      | v1_xboole_0(X0_53) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1697,plain,
% 7.70/1.50      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 7.70/1.50      | r1_xboole_0(X0_53,X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3857,plain,
% 7.70/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1711,c_1697]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_34,negated_conjecture,
% 7.70/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.70/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_43,plain,
% 7.70/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_45,plain,
% 7.70/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2161,plain,
% 7.70/1.50      ( ~ r1_subset_1(sK2,sK3)
% 7.70/1.50      | r1_xboole_0(sK2,sK3)
% 7.70/1.50      | v1_xboole_0(sK3)
% 7.70/1.50      | v1_xboole_0(sK2) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1049]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2162,plain,
% 7.70/1.50      ( r1_subset_1(sK2,sK3) != iProver_top
% 7.70/1.50      | r1_xboole_0(sK2,sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3860,plain,
% 7.70/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_3857,c_41,c_43,c_45,c_2162]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_14,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | v1_partfun1(X0,X1)
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | v1_xboole_0(X2) ),
% 7.70/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_13,plain,
% 7.70/1.50      ( v4_relat_1(X0,X1)
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.70/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17,plain,
% 7.70/1.50      ( ~ v1_partfun1(X0,X1)
% 7.70/1.50      | ~ v4_relat_1(X0,X1)
% 7.70/1.50      | ~ v1_relat_1(X0)
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_396,plain,
% 7.70/1.50      ( ~ v1_partfun1(X0,X1)
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ v1_relat_1(X0)
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(resolution,[status(thm)],[c_13,c_17]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_12,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | v1_relat_1(X0) ),
% 7.70/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_400,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ v1_partfun1(X0,X1)
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_396,c_17,c_13,c_12]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_401,plain,
% 7.70/1.50      ( ~ v1_partfun1(X0,X1)
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_400]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_440,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(resolution,[status(thm)],[c_14,c_401]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_444,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_440,c_17,c_14,c_13,c_12]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_445,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | k1_relat_1(X0) = X1 ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_444]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1025,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.70/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.70/1.50      | ~ v1_funct_1(X0_53)
% 7.70/1.50      | v1_xboole_0(X2_53)
% 7.70/1.50      | k1_relat_1(X0_53) = X1_53 ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_445]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1720,plain,
% 7.70/1.50      ( k1_relat_1(X0_53) = X1_53
% 7.70/1.50      | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1025]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5739,plain,
% 7.70/1.50      ( k1_relat_1(sK4) = sK2
% 7.70/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.70/1.50      | v1_funct_1(sK4) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1708,c_1720]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2210,plain,
% 7.70/1.50      ( ~ v1_funct_2(sK4,X0_53,X1_53)
% 7.70/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.70/1.50      | ~ v1_funct_1(sK4)
% 7.70/1.50      | v1_xboole_0(X1_53)
% 7.70/1.50      | k1_relat_1(sK4) = X0_53 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1025]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2515,plain,
% 7.70/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.70/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.70/1.50      | ~ v1_funct_1(sK4)
% 7.70/1.50      | v1_xboole_0(sK1)
% 7.70/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_2210]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6465,plain,
% 7.70/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_5739,c_37,c_31,c_30,c_29,c_2515]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_7,plain,
% 7.70/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.70/1.50      | ~ v1_relat_1(X0)
% 7.70/1.50      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1052,plain,
% 7.70/1.50      ( ~ r1_xboole_0(k1_relat_1(X0_53),X1_53)
% 7.70/1.50      | ~ v1_relat_1(X0_53)
% 7.70/1.50      | k7_relat_1(X0_53,X1_53) = k1_xboole_0 ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1694,plain,
% 7.70/1.50      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.70/1.50      | r1_xboole_0(k1_relat_1(X0_53),X1_53) != iProver_top
% 7.70/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1052]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6468,plain,
% 7.70/1.50      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.70/1.50      | r1_xboole_0(sK2,X0_53) != iProver_top
% 7.70/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_6465,c_1694]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1047,plain,
% 7.70/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.70/1.50      | v1_relat_1(X0_53) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2107,plain,
% 7.70/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.70/1.50      | v1_relat_1(sK4) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1047]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2108,plain,
% 7.70/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.70/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6568,plain,
% 7.70/1.50      ( r1_xboole_0(sK2,X0_53) != iProver_top
% 7.70/1.50      | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_6468,c_48,c_2108]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6569,plain,
% 7.70/1.50      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.70/1.50      | r1_xboole_0(sK2,X0_53) != iProver_top ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_6568]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6576,plain,
% 7.70/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_3860,c_6569]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1699,plain,
% 7.70/1.50      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.70/1.50      | v1_relat_1(X0_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2913,plain,
% 7.70/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1708,c_1699]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_4,plain,
% 7.70/1.50      ( ~ v1_relat_1(X0)
% 7.70/1.50      | k3_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1055,plain,
% 7.70/1.50      ( ~ v1_relat_1(X0_53)
% 7.70/1.50      | k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1692,plain,
% 7.70/1.50      ( k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
% 7.70/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1055]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3109,plain,
% 7.70/1.50      ( k3_xboole_0(k7_relat_1(sK4,X0_53),k7_relat_1(sK4,X1_53)) = k7_relat_1(sK4,k3_xboole_0(X0_53,X1_53)) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_2913,c_1692]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6723,plain,
% 7.70/1.50      ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k3_xboole_0(k7_relat_1(sK4,X0_53),k1_xboole_0) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_6576,c_3109]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_0,plain,
% 7.70/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1059,plain,
% 7.70/1.50      ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6725,plain,
% 7.70/1.50      ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k1_xboole_0 ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_6723,c_1059]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23182,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_23157,c_2488,c_6725]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_35,negated_conjecture,
% 7.70/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_42,plain,
% 7.70/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_44,plain,
% 7.70/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23344,plain,
% 7.70/1.50      ( v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_23182,c_42,c_43,c_44]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23345,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_23344]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23355,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.50      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_5011,c_23345]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_11,plain,
% 7.70/1.50      ( ~ r1_subset_1(X0,X1)
% 7.70/1.50      | r1_subset_1(X1,X0)
% 7.70/1.50      | v1_xboole_0(X0)
% 7.70/1.50      | v1_xboole_0(X1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1048,plain,
% 7.70/1.50      ( ~ r1_subset_1(X0_53,X1_53)
% 7.70/1.50      | r1_subset_1(X1_53,X0_53)
% 7.70/1.50      | v1_xboole_0(X1_53)
% 7.70/1.50      | v1_xboole_0(X0_53) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1698,plain,
% 7.70/1.50      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 7.70/1.50      | r1_subset_1(X1_53,X0_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1048]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_4598,plain,
% 7.70/1.50      ( r1_subset_1(sK3,sK2) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1711,c_1698]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2158,plain,
% 7.70/1.50      ( r1_subset_1(sK3,sK2)
% 7.70/1.50      | ~ r1_subset_1(sK2,sK3)
% 7.70/1.50      | v1_xboole_0(sK3)
% 7.70/1.50      | v1_xboole_0(sK2) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1048]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2159,plain,
% 7.70/1.50      ( r1_subset_1(sK3,sK2) = iProver_top
% 7.70/1.50      | r1_subset_1(sK2,sK3) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_2158]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5086,plain,
% 7.70/1.50      ( r1_subset_1(sK3,sK2) = iProver_top ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_4598,c_41,c_43,c_45,c_2159]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5092,plain,
% 7.70/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_5086,c_1697]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2376,plain,
% 7.70/1.50      ( ~ r1_subset_1(sK3,sK2)
% 7.70/1.50      | r1_xboole_0(sK3,sK2)
% 7.70/1.50      | v1_xboole_0(sK3)
% 7.70/1.50      | v1_xboole_0(sK2) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1049]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2378,plain,
% 7.70/1.50      ( r1_subset_1(sK3,sK2) != iProver_top
% 7.70/1.50      | r1_xboole_0(sK3,sK2) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_2376]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5167,plain,
% 7.70/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_5092,c_41,c_43,c_45,c_2159,c_2378]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5738,plain,
% 7.70/1.50      ( k1_relat_1(sK5) = sK3
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1705,c_1720]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_27,negated_conjecture,
% 7.70/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.70/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2205,plain,
% 7.70/1.50      ( ~ v1_funct_2(sK5,X0_53,X1_53)
% 7.70/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.70/1.50      | ~ v1_funct_1(sK5)
% 7.70/1.50      | v1_xboole_0(X1_53)
% 7.70/1.50      | k1_relat_1(sK5) = X0_53 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1025]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2512,plain,
% 7.70/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.70/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.70/1.50      | ~ v1_funct_1(sK5)
% 7.70/1.50      | v1_xboole_0(sK1)
% 7.70/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_2205]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6218,plain,
% 7.70/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_5738,c_37,c_28,c_27,c_26,c_2512]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6221,plain,
% 7.70/1.50      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.70/1.50      | r1_xboole_0(sK3,X0_53) != iProver_top
% 7.70/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_6218,c_1694]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_51,plain,
% 7.70/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2104,plain,
% 7.70/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.70/1.50      | v1_relat_1(sK5) ),
% 7.70/1.50      inference(instantiation,[status(thm)],[c_1047]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2105,plain,
% 7.70/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6487,plain,
% 7.70/1.50      ( r1_xboole_0(sK3,X0_53) != iProver_top
% 7.70/1.50      | k7_relat_1(sK5,X0_53) = k1_xboole_0 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_6221,c_51,c_2105]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6488,plain,
% 7.70/1.50      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.70/1.50      | r1_xboole_0(sK3,X0_53) != iProver_top ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_6487]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6495,plain,
% 7.70/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_5167,c_6488]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2912,plain,
% 7.70/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_1705,c_1699]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3,plain,
% 7.70/1.50      ( ~ v1_relat_1(X0)
% 7.70/1.50      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1056,plain,
% 7.70/1.50      ( ~ v1_relat_1(X0_53)
% 7.70/1.50      | k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1691,plain,
% 7.70/1.50      ( k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
% 7.70/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_3100,plain,
% 7.70/1.50      ( k7_relat_1(k7_relat_1(sK5,X0_53),X1_53) = k7_relat_1(sK5,k3_xboole_0(X0_53,X1_53)) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_2912,c_1691]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6926,plain,
% 7.70/1.50      ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k7_relat_1(k1_xboole_0,X0_53) ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_6495,c_3100]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5,plain,
% 7.70/1.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.70/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1054,plain,
% 7.70/1.50      ( k7_relat_1(k1_xboole_0,X0_53) = k1_xboole_0 ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_6932,plain,
% 7.70/1.50      ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k1_xboole_0 ),
% 7.70/1.50      inference(light_normalisation,[status(thm)],[c_6926,c_1054]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23356,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.50      | k1_xboole_0 != k1_xboole_0
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_23355,c_6932]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_23357,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(equality_resolution_simp,[status(thm)],[c_23356]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_21,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.70/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_204,plain,
% 7.70/1.50      ( ~ v1_funct_1(X3)
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X1)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_21,c_24,c_23,c_22]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_205,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.50      | ~ v1_funct_1(X0)
% 7.70/1.50      | ~ v1_funct_1(X3)
% 7.70/1.50      | v1_xboole_0(X1)
% 7.70/1.50      | v1_xboole_0(X2)
% 7.70/1.50      | v1_xboole_0(X4)
% 7.70/1.50      | v1_xboole_0(X5)
% 7.70/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_204]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1027,plain,
% 7.70/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.70/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.70/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.70/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.70/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.70/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.70/1.50      | ~ v1_funct_1(X0_53)
% 7.70/1.50      | ~ v1_funct_1(X3_53)
% 7.70/1.50      | v1_xboole_0(X2_53)
% 7.70/1.50      | v1_xboole_0(X1_53)
% 7.70/1.50      | v1_xboole_0(X4_53)
% 7.70/1.50      | v1_xboole_0(X5_53)
% 7.70/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_205]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1718,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.70/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.70/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.70/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.70/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.70/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_1027]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1929,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
% 7.70/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.70/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.70/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.70/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.70/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(X4_53) = iProver_top ),
% 7.70/1.50      inference(forward_subsumption_resolution,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_1718,c_1690]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_11319,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.70/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.70/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.70/1.50      | v1_funct_1(sK4) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.70/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_5017,c_1929]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_15581,plain,
% 7.70/1.50      ( v1_funct_1(X1_53) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.70/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.70/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_11319,c_40,c_41,c_46,c_47,c_48]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_15582,plain,
% 7.70/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.70/1.50      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.70/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.70/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_15581]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_15599,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_2488,c_15582]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_15624,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_15599,c_2488,c_6725]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17319,plain,
% 7.70/1.50      ( v1_funct_1(X0_53) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4 ),
% 7.70/1.50      inference(global_propositional_subsumption,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_15624,c_42,c_43,c_44]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17320,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.70/1.50      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(X0_53) != iProver_top ),
% 7.70/1.50      inference(renaming,[status(thm)],[c_17319]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17330,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.50      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(superposition,[status(thm)],[c_5011,c_17320]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17331,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.50      | k1_xboole_0 != k1_xboole_0
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_17330,c_6932]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_17332,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.50      inference(equality_resolution_simp,[status(thm)],[c_17331]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_25,negated_conjecture,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.70/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_1041,negated_conjecture,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.70/1.50      inference(subtyping,[status(esa)],[c_25]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_2680,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_2488,c_1041]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5015,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_5011,c_2680]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_5081,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_5015,c_5017]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_7005,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_6725,c_5081]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_11047,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.70/1.50      inference(demodulation,[status(thm)],[c_7005,c_6932]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_11048,plain,
% 7.70/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.70/1.50      inference(equality_resolution_simp,[status(thm)],[c_11047]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_50,plain,
% 7.70/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(c_49,plain,
% 7.70/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.70/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.70/1.50  
% 7.70/1.50  cnf(contradiction,plain,
% 7.70/1.50      ( $false ),
% 7.70/1.50      inference(minisat,
% 7.70/1.50                [status(thm)],
% 7.70/1.50                [c_23357,c_17332,c_11048,c_51,c_50,c_49]) ).
% 7.70/1.50  
% 7.70/1.50  
% 7.70/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.70/1.50  
% 7.70/1.50  ------                               Statistics
% 7.70/1.50  
% 7.70/1.50  ------ Selected
% 7.70/1.50  
% 7.70/1.50  total_time:                             0.995
% 7.70/1.50  
%------------------------------------------------------------------------------
