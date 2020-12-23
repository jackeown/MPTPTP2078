%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:29 EST 2020

% Result     : Theorem 7.47s
% Output     : CNFRefutation 7.47s
% Verified   : 
% Statistics : Number of formulae       :  215 (1273 expanded)
%              Number of clauses        :  124 ( 334 expanded)
%              Number of leaves         :   23 ( 473 expanded)
%              Depth                    :   24
%              Number of atoms          : 1123 (15161 expanded)
%              Number of equality atoms :  398 (3587 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4
          | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK6,X3,X1)
        & v1_funct_1(sK6) ) ) ),
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5
              | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK5,X2,X1)
        & v1_funct_1(sK5) ) ) ),
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4
                  | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
                & v1_funct_2(X5,sK4,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK4) ) ) ),
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4
                      | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X4,sK3,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK3,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2)))
                        & v1_funct_2(X5,X3,sK2)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
                    & v1_funct_2(X4,X2,sK2)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
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
                          ( ( k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK1))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK1))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_2(sK6,sK4,sK2)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & r1_subset_1(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f39,f55,f54,f53,f52,f51,f50])).

fof(f90,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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

fof(f80,plain,(
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

fof(f103,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f16,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f86,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f96,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f79,plain,(
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

fof(f104,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f19,plain,(
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

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f41])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2136,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3236,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2136,c_2150])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_314,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_314])).

cnf(c_398,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_315])).

cnf(c_2128,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_6591,plain,
    ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_3236,c_2128])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2139,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2147,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3933,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_2147])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4003,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3933,c_49])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2142,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3932,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_2147])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_52,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3978,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3932,c_52])).

cnf(c_28,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3981,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_3978,c_28])).

cnf(c_4006,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_4003,c_3981])).

cnf(c_6736,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_6591,c_4006])).

cnf(c_19,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_597,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_598,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_600,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_598,c_39,c_37])).

cnf(c_2124,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2158,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3142,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2124,c_2158])).

cnf(c_6737,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_6736,c_3142])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f103])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_26,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f84])).

cnf(c_233,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_27,c_26,c_25])).

cnf(c_234,plain,
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
    inference(renaming,[status(thm)],[c_233])).

cnf(c_2129,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_4134,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3978,c_2129])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_43,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_46,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_53,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_54,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_6498,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4134,c_43,c_46,c_52,c_53,c_54])).

cnf(c_6499,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6498])).

cnf(c_6505,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4003,c_6499])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_50,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6985,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6505,c_44,c_49,c_50,c_51])).

cnf(c_6986,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6985])).

cnf(c_6992,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6591,c_6986])).

cnf(c_6993,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6992,c_3142])).

cnf(c_6994,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6993,c_6591])).

cnf(c_6995,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6994,c_3142])).

cnf(c_6999,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6995])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f104])).

cnf(c_226,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_27,c_26,c_25])).

cnf(c_227,plain,
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
    inference(renaming,[status(thm)],[c_226])).

cnf(c_2130,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_227])).

cnf(c_6550,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3978,c_2130])).

cnf(c_7482,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6550,c_43,c_46,c_52,c_53,c_54])).

cnf(c_7483,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
    | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7482])).

cnf(c_7489,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4003,c_7483])).

cnf(c_7671,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7489,c_44,c_49,c_50,c_51])).

cnf(c_7672,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7671])).

cnf(c_7678,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6591,c_7672])).

cnf(c_7679,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7678,c_3142])).

cnf(c_7680,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7679,c_6591])).

cnf(c_7681,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7680,c_3142])).

cnf(c_7685,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(sK1)
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7681])).

cnf(c_8251,plain,
    ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6737,c_41,c_38,c_36,c_6999,c_7685])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3459,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_2148])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2152,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_542,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_17])).

cnf(c_2125,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_542])).

cnf(c_7954,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_2125])).

cnf(c_7959,plain,
    ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
    inference(superposition,[status(thm)],[c_3459,c_7954])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2157,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2155,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_402,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_315])).

cnf(c_2126,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_3455,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X2,X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2155,c_2126])).

cnf(c_7105,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_3455])).

cnf(c_7216,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7105,c_2158])).

cnf(c_7557,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2157,c_7216])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2159,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7559,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7557,c_2159])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2149,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7595,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7559,c_2149])).

cnf(c_7913,plain,
    ( k7_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3459,c_7595])).

cnf(c_8032,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7959,c_7913])).

cnf(c_3460,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_2148])).

cnf(c_7960,plain,
    ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_3460,c_7954])).

cnf(c_7914,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3460,c_7595])).

cnf(c_8065,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7960,c_7914])).

cnf(c_8253,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8251,c_8032,c_8065])).

cnf(c_8254,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8253])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.47/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.47/1.51  
% 7.47/1.51  ------  iProver source info
% 7.47/1.51  
% 7.47/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.47/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.47/1.51  git: non_committed_changes: false
% 7.47/1.51  git: last_make_outside_of_git: false
% 7.47/1.51  
% 7.47/1.51  ------ 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options
% 7.47/1.51  
% 7.47/1.51  --out_options                           all
% 7.47/1.51  --tptp_safe_out                         true
% 7.47/1.51  --problem_path                          ""
% 7.47/1.51  --include_path                          ""
% 7.47/1.51  --clausifier                            res/vclausify_rel
% 7.47/1.51  --clausifier_options                    ""
% 7.47/1.51  --stdin                                 false
% 7.47/1.51  --stats_out                             all
% 7.47/1.51  
% 7.47/1.51  ------ General Options
% 7.47/1.51  
% 7.47/1.51  --fof                                   false
% 7.47/1.51  --time_out_real                         305.
% 7.47/1.51  --time_out_virtual                      -1.
% 7.47/1.51  --symbol_type_check                     false
% 7.47/1.51  --clausify_out                          false
% 7.47/1.51  --sig_cnt_out                           false
% 7.47/1.51  --trig_cnt_out                          false
% 7.47/1.51  --trig_cnt_out_tolerance                1.
% 7.47/1.51  --trig_cnt_out_sk_spl                   false
% 7.47/1.51  --abstr_cl_out                          false
% 7.47/1.51  
% 7.47/1.51  ------ Global Options
% 7.47/1.51  
% 7.47/1.51  --schedule                              default
% 7.47/1.51  --add_important_lit                     false
% 7.47/1.51  --prop_solver_per_cl                    1000
% 7.47/1.51  --min_unsat_core                        false
% 7.47/1.51  --soft_assumptions                      false
% 7.47/1.51  --soft_lemma_size                       3
% 7.47/1.51  --prop_impl_unit_size                   0
% 7.47/1.51  --prop_impl_unit                        []
% 7.47/1.51  --share_sel_clauses                     true
% 7.47/1.51  --reset_solvers                         false
% 7.47/1.51  --bc_imp_inh                            [conj_cone]
% 7.47/1.51  --conj_cone_tolerance                   3.
% 7.47/1.51  --extra_neg_conj                        none
% 7.47/1.51  --large_theory_mode                     true
% 7.47/1.51  --prolific_symb_bound                   200
% 7.47/1.51  --lt_threshold                          2000
% 7.47/1.51  --clause_weak_htbl                      true
% 7.47/1.51  --gc_record_bc_elim                     false
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing Options
% 7.47/1.51  
% 7.47/1.51  --preprocessing_flag                    true
% 7.47/1.51  --time_out_prep_mult                    0.1
% 7.47/1.51  --splitting_mode                        input
% 7.47/1.51  --splitting_grd                         true
% 7.47/1.51  --splitting_cvd                         false
% 7.47/1.51  --splitting_cvd_svl                     false
% 7.47/1.51  --splitting_nvd                         32
% 7.47/1.51  --sub_typing                            true
% 7.47/1.51  --prep_gs_sim                           true
% 7.47/1.51  --prep_unflatten                        true
% 7.47/1.51  --prep_res_sim                          true
% 7.47/1.51  --prep_upred                            true
% 7.47/1.51  --prep_sem_filter                       exhaustive
% 7.47/1.51  --prep_sem_filter_out                   false
% 7.47/1.51  --pred_elim                             true
% 7.47/1.51  --res_sim_input                         true
% 7.47/1.51  --eq_ax_congr_red                       true
% 7.47/1.51  --pure_diseq_elim                       true
% 7.47/1.51  --brand_transform                       false
% 7.47/1.51  --non_eq_to_eq                          false
% 7.47/1.51  --prep_def_merge                        true
% 7.47/1.51  --prep_def_merge_prop_impl              false
% 7.47/1.51  --prep_def_merge_mbd                    true
% 7.47/1.51  --prep_def_merge_tr_red                 false
% 7.47/1.51  --prep_def_merge_tr_cl                  false
% 7.47/1.51  --smt_preprocessing                     true
% 7.47/1.51  --smt_ac_axioms                         fast
% 7.47/1.51  --preprocessed_out                      false
% 7.47/1.51  --preprocessed_stats                    false
% 7.47/1.51  
% 7.47/1.51  ------ Abstraction refinement Options
% 7.47/1.51  
% 7.47/1.51  --abstr_ref                             []
% 7.47/1.51  --abstr_ref_prep                        false
% 7.47/1.51  --abstr_ref_until_sat                   false
% 7.47/1.51  --abstr_ref_sig_restrict                funpre
% 7.47/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.51  --abstr_ref_under                       []
% 7.47/1.51  
% 7.47/1.51  ------ SAT Options
% 7.47/1.51  
% 7.47/1.51  --sat_mode                              false
% 7.47/1.51  --sat_fm_restart_options                ""
% 7.47/1.51  --sat_gr_def                            false
% 7.47/1.51  --sat_epr_types                         true
% 7.47/1.51  --sat_non_cyclic_types                  false
% 7.47/1.51  --sat_finite_models                     false
% 7.47/1.51  --sat_fm_lemmas                         false
% 7.47/1.51  --sat_fm_prep                           false
% 7.47/1.51  --sat_fm_uc_incr                        true
% 7.47/1.51  --sat_out_model                         small
% 7.47/1.51  --sat_out_clauses                       false
% 7.47/1.51  
% 7.47/1.51  ------ QBF Options
% 7.47/1.51  
% 7.47/1.51  --qbf_mode                              false
% 7.47/1.51  --qbf_elim_univ                         false
% 7.47/1.51  --qbf_dom_inst                          none
% 7.47/1.51  --qbf_dom_pre_inst                      false
% 7.47/1.51  --qbf_sk_in                             false
% 7.47/1.51  --qbf_pred_elim                         true
% 7.47/1.51  --qbf_split                             512
% 7.47/1.51  
% 7.47/1.51  ------ BMC1 Options
% 7.47/1.51  
% 7.47/1.51  --bmc1_incremental                      false
% 7.47/1.51  --bmc1_axioms                           reachable_all
% 7.47/1.51  --bmc1_min_bound                        0
% 7.47/1.51  --bmc1_max_bound                        -1
% 7.47/1.51  --bmc1_max_bound_default                -1
% 7.47/1.51  --bmc1_symbol_reachability              true
% 7.47/1.51  --bmc1_property_lemmas                  false
% 7.47/1.51  --bmc1_k_induction                      false
% 7.47/1.51  --bmc1_non_equiv_states                 false
% 7.47/1.51  --bmc1_deadlock                         false
% 7.47/1.51  --bmc1_ucm                              false
% 7.47/1.51  --bmc1_add_unsat_core                   none
% 7.47/1.51  --bmc1_unsat_core_children              false
% 7.47/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.51  --bmc1_out_stat                         full
% 7.47/1.51  --bmc1_ground_init                      false
% 7.47/1.51  --bmc1_pre_inst_next_state              false
% 7.47/1.51  --bmc1_pre_inst_state                   false
% 7.47/1.51  --bmc1_pre_inst_reach_state             false
% 7.47/1.51  --bmc1_out_unsat_core                   false
% 7.47/1.51  --bmc1_aig_witness_out                  false
% 7.47/1.51  --bmc1_verbose                          false
% 7.47/1.51  --bmc1_dump_clauses_tptp                false
% 7.47/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.51  --bmc1_dump_file                        -
% 7.47/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.51  --bmc1_ucm_extend_mode                  1
% 7.47/1.51  --bmc1_ucm_init_mode                    2
% 7.47/1.51  --bmc1_ucm_cone_mode                    none
% 7.47/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.51  --bmc1_ucm_relax_model                  4
% 7.47/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.51  --bmc1_ucm_layered_model                none
% 7.47/1.51  --bmc1_ucm_max_lemma_size               10
% 7.47/1.51  
% 7.47/1.51  ------ AIG Options
% 7.47/1.51  
% 7.47/1.51  --aig_mode                              false
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation Options
% 7.47/1.51  
% 7.47/1.51  --instantiation_flag                    true
% 7.47/1.51  --inst_sos_flag                         true
% 7.47/1.51  --inst_sos_phase                        true
% 7.47/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel_side                     num_symb
% 7.47/1.51  --inst_solver_per_active                1400
% 7.47/1.51  --inst_solver_calls_frac                1.
% 7.47/1.51  --inst_passive_queue_type               priority_queues
% 7.47/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.51  --inst_passive_queues_freq              [25;2]
% 7.47/1.51  --inst_dismatching                      true
% 7.47/1.51  --inst_eager_unprocessed_to_passive     true
% 7.47/1.51  --inst_prop_sim_given                   true
% 7.47/1.51  --inst_prop_sim_new                     false
% 7.47/1.51  --inst_subs_new                         false
% 7.47/1.51  --inst_eq_res_simp                      false
% 7.47/1.51  --inst_subs_given                       false
% 7.47/1.51  --inst_orphan_elimination               true
% 7.47/1.51  --inst_learning_loop_flag               true
% 7.47/1.51  --inst_learning_start                   3000
% 7.47/1.51  --inst_learning_factor                  2
% 7.47/1.51  --inst_start_prop_sim_after_learn       3
% 7.47/1.51  --inst_sel_renew                        solver
% 7.47/1.51  --inst_lit_activity_flag                true
% 7.47/1.51  --inst_restr_to_given                   false
% 7.47/1.51  --inst_activity_threshold               500
% 7.47/1.51  --inst_out_proof                        true
% 7.47/1.51  
% 7.47/1.51  ------ Resolution Options
% 7.47/1.51  
% 7.47/1.51  --resolution_flag                       true
% 7.47/1.51  --res_lit_sel                           adaptive
% 7.47/1.51  --res_lit_sel_side                      none
% 7.47/1.51  --res_ordering                          kbo
% 7.47/1.51  --res_to_prop_solver                    active
% 7.47/1.51  --res_prop_simpl_new                    false
% 7.47/1.51  --res_prop_simpl_given                  true
% 7.47/1.51  --res_passive_queue_type                priority_queues
% 7.47/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.51  --res_passive_queues_freq               [15;5]
% 7.47/1.51  --res_forward_subs                      full
% 7.47/1.51  --res_backward_subs                     full
% 7.47/1.51  --res_forward_subs_resolution           true
% 7.47/1.51  --res_backward_subs_resolution          true
% 7.47/1.51  --res_orphan_elimination                true
% 7.47/1.51  --res_time_limit                        2.
% 7.47/1.51  --res_out_proof                         true
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Options
% 7.47/1.51  
% 7.47/1.51  --superposition_flag                    true
% 7.47/1.51  --sup_passive_queue_type                priority_queues
% 7.47/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.51  --demod_completeness_check              fast
% 7.47/1.51  --demod_use_ground                      true
% 7.47/1.51  --sup_to_prop_solver                    passive
% 7.47/1.51  --sup_prop_simpl_new                    true
% 7.47/1.51  --sup_prop_simpl_given                  true
% 7.47/1.51  --sup_fun_splitting                     true
% 7.47/1.51  --sup_smt_interval                      50000
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Simplification Setup
% 7.47/1.51  
% 7.47/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.47/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.47/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.47/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.47/1.51  --sup_immed_triv                        [TrivRules]
% 7.47/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_bw_main                     []
% 7.47/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.47/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_input_bw                          []
% 7.47/1.51  
% 7.47/1.51  ------ Combination Options
% 7.47/1.51  
% 7.47/1.51  --comb_res_mult                         3
% 7.47/1.51  --comb_sup_mult                         2
% 7.47/1.51  --comb_inst_mult                        10
% 7.47/1.51  
% 7.47/1.51  ------ Debug Options
% 7.47/1.51  
% 7.47/1.51  --dbg_backtrace                         false
% 7.47/1.51  --dbg_dump_prop_clauses                 false
% 7.47/1.51  --dbg_dump_prop_clauses_file            -
% 7.47/1.51  --dbg_out_stat                          false
% 7.47/1.51  ------ Parsing...
% 7.47/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.47/1.51  ------ Proving...
% 7.47/1.51  ------ Problem Properties 
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  clauses                                 37
% 7.47/1.51  conjectures                             13
% 7.47/1.51  EPR                                     15
% 7.47/1.51  Horn                                    29
% 7.47/1.51  unary                                   15
% 7.47/1.51  binary                                  8
% 7.47/1.51  lits                                    139
% 7.47/1.51  lits eq                                 16
% 7.47/1.51  fd_pure                                 0
% 7.47/1.51  fd_pseudo                               0
% 7.47/1.51  fd_cond                                 0
% 7.47/1.51  fd_pseudo_cond                          1
% 7.47/1.51  AC symbols                              0
% 7.47/1.51  
% 7.47/1.51  ------ Schedule dynamic 5 is on 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  ------ 
% 7.47/1.51  Current options:
% 7.47/1.51  ------ 
% 7.47/1.51  
% 7.47/1.51  ------ Input Options
% 7.47/1.51  
% 7.47/1.51  --out_options                           all
% 7.47/1.51  --tptp_safe_out                         true
% 7.47/1.51  --problem_path                          ""
% 7.47/1.51  --include_path                          ""
% 7.47/1.51  --clausifier                            res/vclausify_rel
% 7.47/1.51  --clausifier_options                    ""
% 7.47/1.51  --stdin                                 false
% 7.47/1.51  --stats_out                             all
% 7.47/1.51  
% 7.47/1.51  ------ General Options
% 7.47/1.51  
% 7.47/1.51  --fof                                   false
% 7.47/1.51  --time_out_real                         305.
% 7.47/1.51  --time_out_virtual                      -1.
% 7.47/1.51  --symbol_type_check                     false
% 7.47/1.51  --clausify_out                          false
% 7.47/1.51  --sig_cnt_out                           false
% 7.47/1.51  --trig_cnt_out                          false
% 7.47/1.51  --trig_cnt_out_tolerance                1.
% 7.47/1.51  --trig_cnt_out_sk_spl                   false
% 7.47/1.51  --abstr_cl_out                          false
% 7.47/1.51  
% 7.47/1.51  ------ Global Options
% 7.47/1.51  
% 7.47/1.51  --schedule                              default
% 7.47/1.51  --add_important_lit                     false
% 7.47/1.51  --prop_solver_per_cl                    1000
% 7.47/1.51  --min_unsat_core                        false
% 7.47/1.51  --soft_assumptions                      false
% 7.47/1.51  --soft_lemma_size                       3
% 7.47/1.51  --prop_impl_unit_size                   0
% 7.47/1.51  --prop_impl_unit                        []
% 7.47/1.51  --share_sel_clauses                     true
% 7.47/1.51  --reset_solvers                         false
% 7.47/1.51  --bc_imp_inh                            [conj_cone]
% 7.47/1.51  --conj_cone_tolerance                   3.
% 7.47/1.51  --extra_neg_conj                        none
% 7.47/1.51  --large_theory_mode                     true
% 7.47/1.51  --prolific_symb_bound                   200
% 7.47/1.51  --lt_threshold                          2000
% 7.47/1.51  --clause_weak_htbl                      true
% 7.47/1.51  --gc_record_bc_elim                     false
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing Options
% 7.47/1.51  
% 7.47/1.51  --preprocessing_flag                    true
% 7.47/1.51  --time_out_prep_mult                    0.1
% 7.47/1.51  --splitting_mode                        input
% 7.47/1.51  --splitting_grd                         true
% 7.47/1.51  --splitting_cvd                         false
% 7.47/1.51  --splitting_cvd_svl                     false
% 7.47/1.51  --splitting_nvd                         32
% 7.47/1.51  --sub_typing                            true
% 7.47/1.51  --prep_gs_sim                           true
% 7.47/1.51  --prep_unflatten                        true
% 7.47/1.51  --prep_res_sim                          true
% 7.47/1.51  --prep_upred                            true
% 7.47/1.51  --prep_sem_filter                       exhaustive
% 7.47/1.51  --prep_sem_filter_out                   false
% 7.47/1.51  --pred_elim                             true
% 7.47/1.51  --res_sim_input                         true
% 7.47/1.51  --eq_ax_congr_red                       true
% 7.47/1.51  --pure_diseq_elim                       true
% 7.47/1.51  --brand_transform                       false
% 7.47/1.51  --non_eq_to_eq                          false
% 7.47/1.51  --prep_def_merge                        true
% 7.47/1.51  --prep_def_merge_prop_impl              false
% 7.47/1.51  --prep_def_merge_mbd                    true
% 7.47/1.51  --prep_def_merge_tr_red                 false
% 7.47/1.51  --prep_def_merge_tr_cl                  false
% 7.47/1.51  --smt_preprocessing                     true
% 7.47/1.51  --smt_ac_axioms                         fast
% 7.47/1.51  --preprocessed_out                      false
% 7.47/1.51  --preprocessed_stats                    false
% 7.47/1.51  
% 7.47/1.51  ------ Abstraction refinement Options
% 7.47/1.51  
% 7.47/1.51  --abstr_ref                             []
% 7.47/1.51  --abstr_ref_prep                        false
% 7.47/1.51  --abstr_ref_until_sat                   false
% 7.47/1.51  --abstr_ref_sig_restrict                funpre
% 7.47/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.47/1.51  --abstr_ref_under                       []
% 7.47/1.51  
% 7.47/1.51  ------ SAT Options
% 7.47/1.51  
% 7.47/1.51  --sat_mode                              false
% 7.47/1.51  --sat_fm_restart_options                ""
% 7.47/1.51  --sat_gr_def                            false
% 7.47/1.51  --sat_epr_types                         true
% 7.47/1.51  --sat_non_cyclic_types                  false
% 7.47/1.51  --sat_finite_models                     false
% 7.47/1.51  --sat_fm_lemmas                         false
% 7.47/1.51  --sat_fm_prep                           false
% 7.47/1.51  --sat_fm_uc_incr                        true
% 7.47/1.51  --sat_out_model                         small
% 7.47/1.51  --sat_out_clauses                       false
% 7.47/1.51  
% 7.47/1.51  ------ QBF Options
% 7.47/1.51  
% 7.47/1.51  --qbf_mode                              false
% 7.47/1.51  --qbf_elim_univ                         false
% 7.47/1.51  --qbf_dom_inst                          none
% 7.47/1.51  --qbf_dom_pre_inst                      false
% 7.47/1.51  --qbf_sk_in                             false
% 7.47/1.51  --qbf_pred_elim                         true
% 7.47/1.51  --qbf_split                             512
% 7.47/1.51  
% 7.47/1.51  ------ BMC1 Options
% 7.47/1.51  
% 7.47/1.51  --bmc1_incremental                      false
% 7.47/1.51  --bmc1_axioms                           reachable_all
% 7.47/1.51  --bmc1_min_bound                        0
% 7.47/1.51  --bmc1_max_bound                        -1
% 7.47/1.51  --bmc1_max_bound_default                -1
% 7.47/1.51  --bmc1_symbol_reachability              true
% 7.47/1.51  --bmc1_property_lemmas                  false
% 7.47/1.51  --bmc1_k_induction                      false
% 7.47/1.51  --bmc1_non_equiv_states                 false
% 7.47/1.51  --bmc1_deadlock                         false
% 7.47/1.51  --bmc1_ucm                              false
% 7.47/1.51  --bmc1_add_unsat_core                   none
% 7.47/1.51  --bmc1_unsat_core_children              false
% 7.47/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.47/1.51  --bmc1_out_stat                         full
% 7.47/1.51  --bmc1_ground_init                      false
% 7.47/1.51  --bmc1_pre_inst_next_state              false
% 7.47/1.51  --bmc1_pre_inst_state                   false
% 7.47/1.51  --bmc1_pre_inst_reach_state             false
% 7.47/1.51  --bmc1_out_unsat_core                   false
% 7.47/1.51  --bmc1_aig_witness_out                  false
% 7.47/1.51  --bmc1_verbose                          false
% 7.47/1.51  --bmc1_dump_clauses_tptp                false
% 7.47/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.47/1.51  --bmc1_dump_file                        -
% 7.47/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.47/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.47/1.51  --bmc1_ucm_extend_mode                  1
% 7.47/1.51  --bmc1_ucm_init_mode                    2
% 7.47/1.51  --bmc1_ucm_cone_mode                    none
% 7.47/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.47/1.51  --bmc1_ucm_relax_model                  4
% 7.47/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.47/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.47/1.51  --bmc1_ucm_layered_model                none
% 7.47/1.51  --bmc1_ucm_max_lemma_size               10
% 7.47/1.51  
% 7.47/1.51  ------ AIG Options
% 7.47/1.51  
% 7.47/1.51  --aig_mode                              false
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation Options
% 7.47/1.51  
% 7.47/1.51  --instantiation_flag                    true
% 7.47/1.51  --inst_sos_flag                         true
% 7.47/1.51  --inst_sos_phase                        true
% 7.47/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.47/1.51  --inst_lit_sel_side                     none
% 7.47/1.51  --inst_solver_per_active                1400
% 7.47/1.51  --inst_solver_calls_frac                1.
% 7.47/1.51  --inst_passive_queue_type               priority_queues
% 7.47/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.47/1.51  --inst_passive_queues_freq              [25;2]
% 7.47/1.51  --inst_dismatching                      true
% 7.47/1.51  --inst_eager_unprocessed_to_passive     true
% 7.47/1.51  --inst_prop_sim_given                   true
% 7.47/1.51  --inst_prop_sim_new                     false
% 7.47/1.51  --inst_subs_new                         false
% 7.47/1.51  --inst_eq_res_simp                      false
% 7.47/1.51  --inst_subs_given                       false
% 7.47/1.51  --inst_orphan_elimination               true
% 7.47/1.51  --inst_learning_loop_flag               true
% 7.47/1.51  --inst_learning_start                   3000
% 7.47/1.51  --inst_learning_factor                  2
% 7.47/1.51  --inst_start_prop_sim_after_learn       3
% 7.47/1.51  --inst_sel_renew                        solver
% 7.47/1.51  --inst_lit_activity_flag                true
% 7.47/1.51  --inst_restr_to_given                   false
% 7.47/1.51  --inst_activity_threshold               500
% 7.47/1.51  --inst_out_proof                        true
% 7.47/1.51  
% 7.47/1.51  ------ Resolution Options
% 7.47/1.51  
% 7.47/1.51  --resolution_flag                       false
% 7.47/1.51  --res_lit_sel                           adaptive
% 7.47/1.51  --res_lit_sel_side                      none
% 7.47/1.51  --res_ordering                          kbo
% 7.47/1.51  --res_to_prop_solver                    active
% 7.47/1.51  --res_prop_simpl_new                    false
% 7.47/1.51  --res_prop_simpl_given                  true
% 7.47/1.51  --res_passive_queue_type                priority_queues
% 7.47/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.47/1.51  --res_passive_queues_freq               [15;5]
% 7.47/1.51  --res_forward_subs                      full
% 7.47/1.51  --res_backward_subs                     full
% 7.47/1.51  --res_forward_subs_resolution           true
% 7.47/1.51  --res_backward_subs_resolution          true
% 7.47/1.51  --res_orphan_elimination                true
% 7.47/1.51  --res_time_limit                        2.
% 7.47/1.51  --res_out_proof                         true
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Options
% 7.47/1.51  
% 7.47/1.51  --superposition_flag                    true
% 7.47/1.51  --sup_passive_queue_type                priority_queues
% 7.47/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.47/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.47/1.51  --demod_completeness_check              fast
% 7.47/1.51  --demod_use_ground                      true
% 7.47/1.51  --sup_to_prop_solver                    passive
% 7.47/1.51  --sup_prop_simpl_new                    true
% 7.47/1.51  --sup_prop_simpl_given                  true
% 7.47/1.51  --sup_fun_splitting                     true
% 7.47/1.51  --sup_smt_interval                      50000
% 7.47/1.51  
% 7.47/1.51  ------ Superposition Simplification Setup
% 7.47/1.51  
% 7.47/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.47/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.47/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.47/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.47/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.47/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.47/1.51  --sup_immed_triv                        [TrivRules]
% 7.47/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_immed_bw_main                     []
% 7.47/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.47/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.47/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.47/1.51  --sup_input_bw                          []
% 7.47/1.51  
% 7.47/1.51  ------ Combination Options
% 7.47/1.51  
% 7.47/1.51  --comb_res_mult                         3
% 7.47/1.51  --comb_sup_mult                         2
% 7.47/1.51  --comb_inst_mult                        10
% 7.47/1.51  
% 7.47/1.51  ------ Debug Options
% 7.47/1.51  
% 7.47/1.51  --dbg_backtrace                         false
% 7.47/1.51  --dbg_dump_prop_clauses                 false
% 7.47/1.51  --dbg_dump_prop_clauses_file            -
% 7.47/1.51  --dbg_out_stat                          false
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  ------ Proving...
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  % SZS status Theorem for theBenchmark.p
% 7.47/1.51  
% 7.47/1.51   Resolution empty clause
% 7.47/1.51  
% 7.47/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  fof(f17,conjecture,(
% 7.47/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f18,negated_conjecture,(
% 7.47/1.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.47/1.51    inference(negated_conjecture,[],[f17])).
% 7.47/1.51  
% 7.47/1.51  fof(f38,plain,(
% 7.47/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.47/1.51    inference(ennf_transformation,[],[f18])).
% 7.47/1.51  
% 7.47/1.51  fof(f39,plain,(
% 7.47/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.47/1.51    inference(flattening,[],[f38])).
% 7.47/1.51  
% 7.47/1.51  fof(f55,plain,(
% 7.47/1.51    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f54,plain,(
% 7.47/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f53,plain,(
% 7.47/1.51    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f52,plain,(
% 7.47/1.51    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f51,plain,(
% 7.47/1.51    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f50,plain,(
% 7.47/1.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f56,plain,(
% 7.47/1.51    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 7.47/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f39,f55,f54,f53,f52,f51,f50])).
% 7.47/1.51  
% 7.47/1.51  fof(f90,plain,(
% 7.47/1.51    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f7,axiom,(
% 7.47/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f45,plain,(
% 7.47/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.47/1.51    inference(nnf_transformation,[],[f7])).
% 7.47/1.51  
% 7.47/1.51  fof(f68,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.47/1.51    inference(cnf_transformation,[],[f45])).
% 7.47/1.51  
% 7.47/1.51  fof(f5,axiom,(
% 7.47/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f21,plain,(
% 7.47/1.51    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.47/1.51    inference(ennf_transformation,[],[f5])).
% 7.47/1.51  
% 7.47/1.51  fof(f66,plain,(
% 7.47/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.47/1.51    inference(cnf_transformation,[],[f21])).
% 7.47/1.51  
% 7.47/1.51  fof(f69,plain,(
% 7.47/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f45])).
% 7.47/1.51  
% 7.47/1.51  fof(f94,plain,(
% 7.47/1.51    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f14,axiom,(
% 7.47/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f32,plain,(
% 7.47/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.47/1.51    inference(ennf_transformation,[],[f14])).
% 7.47/1.51  
% 7.47/1.51  fof(f33,plain,(
% 7.47/1.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.47/1.51    inference(flattening,[],[f32])).
% 7.47/1.51  
% 7.47/1.51  fof(f78,plain,(
% 7.47/1.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f33])).
% 7.47/1.51  
% 7.47/1.51  fof(f92,plain,(
% 7.47/1.51    v1_funct_1(sK5)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f97,plain,(
% 7.47/1.51    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f95,plain,(
% 7.47/1.51    v1_funct_1(sK6)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f98,plain,(
% 7.47/1.51    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f12,axiom,(
% 7.47/1.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f29,plain,(
% 7.47/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.47/1.51    inference(ennf_transformation,[],[f12])).
% 7.47/1.51  
% 7.47/1.51  fof(f30,plain,(
% 7.47/1.51    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.47/1.51    inference(flattening,[],[f29])).
% 7.47/1.51  
% 7.47/1.51  fof(f47,plain,(
% 7.47/1.51    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.47/1.51    inference(nnf_transformation,[],[f30])).
% 7.47/1.51  
% 7.47/1.51  fof(f75,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f47])).
% 7.47/1.51  
% 7.47/1.51  fof(f91,plain,(
% 7.47/1.51    r1_subset_1(sK3,sK4)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f87,plain,(
% 7.47/1.51    ~v1_xboole_0(sK3)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f89,plain,(
% 7.47/1.51    ~v1_xboole_0(sK4)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f1,axiom,(
% 7.47/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f40,plain,(
% 7.47/1.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.47/1.51    inference(nnf_transformation,[],[f1])).
% 7.47/1.51  
% 7.47/1.51  fof(f57,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f40])).
% 7.47/1.51  
% 7.47/1.51  fof(f85,plain,(
% 7.47/1.51    ~v1_xboole_0(sK1)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f88,plain,(
% 7.47/1.51    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f15,axiom,(
% 7.47/1.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f34,plain,(
% 7.47/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.47/1.51    inference(ennf_transformation,[],[f15])).
% 7.47/1.51  
% 7.47/1.51  fof(f35,plain,(
% 7.47/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.47/1.51    inference(flattening,[],[f34])).
% 7.47/1.51  
% 7.47/1.51  fof(f48,plain,(
% 7.47/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.47/1.51    inference(nnf_transformation,[],[f35])).
% 7.47/1.51  
% 7.47/1.51  fof(f49,plain,(
% 7.47/1.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.47/1.51    inference(flattening,[],[f48])).
% 7.47/1.51  
% 7.47/1.51  fof(f80,plain,(
% 7.47/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f49])).
% 7.47/1.51  
% 7.47/1.51  fof(f103,plain,(
% 7.47/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(equality_resolution,[],[f80])).
% 7.47/1.51  
% 7.47/1.51  fof(f16,axiom,(
% 7.47/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f36,plain,(
% 7.47/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.47/1.51    inference(ennf_transformation,[],[f16])).
% 7.47/1.51  
% 7.47/1.51  fof(f37,plain,(
% 7.47/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.47/1.51    inference(flattening,[],[f36])).
% 7.47/1.51  
% 7.47/1.51  fof(f82,plain,(
% 7.47/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f37])).
% 7.47/1.51  
% 7.47/1.51  fof(f83,plain,(
% 7.47/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f37])).
% 7.47/1.51  
% 7.47/1.51  fof(f84,plain,(
% 7.47/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f37])).
% 7.47/1.51  
% 7.47/1.51  fof(f86,plain,(
% 7.47/1.51    ~v1_xboole_0(sK2)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f96,plain,(
% 7.47/1.51    v1_funct_2(sK6,sK4,sK2)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f93,plain,(
% 7.47/1.51    v1_funct_2(sK5,sK3,sK2)),
% 7.47/1.51    inference(cnf_transformation,[],[f56])).
% 7.47/1.51  
% 7.47/1.51  fof(f79,plain,(
% 7.47/1.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f49])).
% 7.47/1.51  
% 7.47/1.51  fof(f104,plain,(
% 7.47/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.47/1.51    inference(equality_resolution,[],[f79])).
% 7.47/1.51  
% 7.47/1.51  fof(f13,axiom,(
% 7.47/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f31,plain,(
% 7.47/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.47/1.51    inference(ennf_transformation,[],[f13])).
% 7.47/1.51  
% 7.47/1.51  fof(f77,plain,(
% 7.47/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.47/1.51    inference(cnf_transformation,[],[f31])).
% 7.47/1.51  
% 7.47/1.51  fof(f4,axiom,(
% 7.47/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f43,plain,(
% 7.47/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.47/1.51    inference(nnf_transformation,[],[f4])).
% 7.47/1.51  
% 7.47/1.51  fof(f44,plain,(
% 7.47/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.47/1.51    inference(flattening,[],[f43])).
% 7.47/1.51  
% 7.47/1.51  fof(f64,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.47/1.51    inference(cnf_transformation,[],[f44])).
% 7.47/1.51  
% 7.47/1.51  fof(f99,plain,(
% 7.47/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.47/1.51    inference(equality_resolution,[],[f64])).
% 7.47/1.51  
% 7.47/1.51  fof(f9,axiom,(
% 7.47/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f24,plain,(
% 7.47/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.47/1.51    inference(ennf_transformation,[],[f9])).
% 7.47/1.51  
% 7.47/1.51  fof(f46,plain,(
% 7.47/1.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.47/1.51    inference(nnf_transformation,[],[f24])).
% 7.47/1.51  
% 7.47/1.51  fof(f72,plain,(
% 7.47/1.51    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f46])).
% 7.47/1.51  
% 7.47/1.51  fof(f11,axiom,(
% 7.47/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f27,plain,(
% 7.47/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.47/1.51    inference(ennf_transformation,[],[f11])).
% 7.47/1.51  
% 7.47/1.51  fof(f28,plain,(
% 7.47/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.47/1.51    inference(flattening,[],[f27])).
% 7.47/1.51  
% 7.47/1.51  fof(f74,plain,(
% 7.47/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f28])).
% 7.47/1.51  
% 7.47/1.51  fof(f2,axiom,(
% 7.47/1.51    v1_xboole_0(k1_xboole_0)),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f59,plain,(
% 7.47/1.51    v1_xboole_0(k1_xboole_0)),
% 7.47/1.51    inference(cnf_transformation,[],[f2])).
% 7.47/1.51  
% 7.47/1.51  fof(f3,axiom,(
% 7.47/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f19,plain,(
% 7.47/1.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 7.47/1.51    inference(rectify,[],[f3])).
% 7.47/1.51  
% 7.47/1.51  fof(f20,plain,(
% 7.47/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 7.47/1.51    inference(ennf_transformation,[],[f19])).
% 7.47/1.51  
% 7.47/1.51  fof(f41,plain,(
% 7.47/1.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.47/1.51    introduced(choice_axiom,[])).
% 7.47/1.51  
% 7.47/1.51  fof(f42,plain,(
% 7.47/1.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 7.47/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f41])).
% 7.47/1.51  
% 7.47/1.51  fof(f61,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f42])).
% 7.47/1.51  
% 7.47/1.51  fof(f8,axiom,(
% 7.47/1.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f23,plain,(
% 7.47/1.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.47/1.51    inference(ennf_transformation,[],[f8])).
% 7.47/1.51  
% 7.47/1.51  fof(f70,plain,(
% 7.47/1.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f23])).
% 7.47/1.51  
% 7.47/1.51  fof(f58,plain,(
% 7.47/1.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.47/1.51    inference(cnf_transformation,[],[f40])).
% 7.47/1.51  
% 7.47/1.51  fof(f10,axiom,(
% 7.47/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.47/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.47/1.51  
% 7.47/1.51  fof(f25,plain,(
% 7.47/1.51    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.47/1.51    inference(ennf_transformation,[],[f10])).
% 7.47/1.51  
% 7.47/1.51  fof(f26,plain,(
% 7.47/1.51    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.47/1.51    inference(flattening,[],[f25])).
% 7.47/1.51  
% 7.47/1.51  fof(f73,plain,(
% 7.47/1.51    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.47/1.51    inference(cnf_transformation,[],[f26])).
% 7.47/1.51  
% 7.47/1.51  cnf(c_36,negated_conjecture,
% 7.47/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2136,plain,
% 7.47/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_12,plain,
% 7.47/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2150,plain,
% 7.47/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.47/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3236,plain,
% 7.47/1.51      ( r1_tarski(sK4,sK1) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2136,c_2150]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_9,plain,
% 7.47/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.47/1.51      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.47/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_11,plain,
% 7.47/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_314,plain,
% 7.47/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.47/1.51      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_315,plain,
% 7.47/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_314]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_398,plain,
% 7.47/1.51      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.47/1.51      inference(bin_hyper_res,[status(thm)],[c_9,c_315]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2128,plain,
% 7.47/1.51      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 7.47/1.51      | r1_tarski(X2,X0) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6591,plain,
% 7.47/1.51      ( k9_subset_1(sK1,X0,sK4) = k3_xboole_0(X0,sK4) ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3236,c_2128]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_32,negated_conjecture,
% 7.47/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 7.47/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2139,plain,
% 7.47/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_21,plain,
% 7.47/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.47/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2147,plain,
% 7.47/1.51      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 7.47/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.47/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3933,plain,
% 7.47/1.51      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 7.47/1.51      | v1_funct_1(sK5) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2139,c_2147]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_34,negated_conjecture,
% 7.47/1.51      ( v1_funct_1(sK5) ),
% 7.47/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_49,plain,
% 7.47/1.51      ( v1_funct_1(sK5) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4003,plain,
% 7.47/1.51      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 7.47/1.51      inference(global_propositional_subsumption,[status(thm)],[c_3933,c_49]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_29,negated_conjecture,
% 7.47/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 7.47/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2142,plain,
% 7.47/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3932,plain,
% 7.47/1.51      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 7.47/1.51      | v1_funct_1(sK6) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2142,c_2147]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_31,negated_conjecture,
% 7.47/1.51      ( v1_funct_1(sK6) ),
% 7.47/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_52,plain,
% 7.47/1.51      ( v1_funct_1(sK6) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3978,plain,
% 7.47/1.51      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 7.47/1.51      inference(global_propositional_subsumption,[status(thm)],[c_3932,c_52]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_28,negated_conjecture,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.47/1.51      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3981,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.47/1.51      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_3978,c_28]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4006,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.47/1.51      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_4003,c_3981]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6736,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.47/1.51      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4)) ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_6591,c_4006]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_19,plain,
% 7.47/1.51      ( ~ r1_subset_1(X0,X1)
% 7.47/1.51      | r1_xboole_0(X0,X1)
% 7.47/1.51      | v1_xboole_0(X0)
% 7.47/1.51      | v1_xboole_0(X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f75]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_35,negated_conjecture,
% 7.47/1.51      ( r1_subset_1(sK3,sK4) ),
% 7.47/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_597,plain,
% 7.47/1.51      ( r1_xboole_0(X0,X1)
% 7.47/1.51      | v1_xboole_0(X0)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | sK4 != X1
% 7.47/1.51      | sK3 != X0 ),
% 7.47/1.51      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_598,plain,
% 7.47/1.51      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 7.47/1.51      inference(unflattening,[status(thm)],[c_597]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_39,negated_conjecture,
% 7.47/1.51      ( ~ v1_xboole_0(sK3) ),
% 7.47/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_37,negated_conjecture,
% 7.47/1.51      ( ~ v1_xboole_0(sK4) ),
% 7.47/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_600,plain,
% 7.47/1.51      ( r1_xboole_0(sK3,sK4) ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_598,c_39,c_37]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2124,plain,
% 7.47/1.51      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_1,plain,
% 7.47/1.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2158,plain,
% 7.47/1.51      ( k3_xboole_0(X0,X1) = k1_xboole_0 | r1_xboole_0(X0,X1) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3142,plain,
% 7.47/1.51      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2124,c_2158]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6737,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 7.47/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_6736,c_3142]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_41,negated_conjecture,
% 7.47/1.51      ( ~ v1_xboole_0(sK1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_38,negated_conjecture,
% 7.47/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.47/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_23,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_27,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_26,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_25,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_233,plain,
% 7.47/1.51      ( ~ v1_funct_1(X3)
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_23,c_27,c_26,c_25]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_234,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_233]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2129,plain,
% 7.47/1.51      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 7.47/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.47/1.51      | v1_funct_2(X5,X4,X1) != iProver_top
% 7.47/1.51      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 7.47/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.47/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 7.47/1.51      | v1_funct_1(X2) != iProver_top
% 7.47/1.51      | v1_funct_1(X5) != iProver_top
% 7.47/1.51      | v1_xboole_0(X3) = iProver_top
% 7.47/1.51      | v1_xboole_0(X1) = iProver_top
% 7.47/1.51      | v1_xboole_0(X4) = iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4134,plain,
% 7.47/1.51      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 7.47/1.51      | v1_funct_2(X1,X0,sK2) != iProver_top
% 7.47/1.51      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | v1_funct_1(X1) != iProver_top
% 7.47/1.51      | v1_funct_1(sK6) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(X2) = iProver_top
% 7.47/1.51      | v1_xboole_0(sK2) = iProver_top
% 7.47/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3978,c_2129]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_40,negated_conjecture,
% 7.47/1.51      ( ~ v1_xboole_0(sK2) ),
% 7.47/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_43,plain,
% 7.47/1.51      ( v1_xboole_0(sK2) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_46,plain,
% 7.47/1.51      ( v1_xboole_0(sK4) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_30,negated_conjecture,
% 7.47/1.51      ( v1_funct_2(sK6,sK4,sK2) ),
% 7.47/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_53,plain,
% 7.47/1.51      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_54,plain,
% 7.47/1.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6498,plain,
% 7.47/1.51      ( v1_funct_1(X1) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | v1_funct_2(X1,X0,sK2) != iProver_top
% 7.47/1.51      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 7.47/1.51      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(X2) = iProver_top ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_4134,c_43,c_46,c_52,c_53,c_54]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6499,plain,
% 7.47/1.51      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),sK4) = sK6
% 7.47/1.51      | v1_funct_2(X1,X0,sK2) != iProver_top
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | v1_funct_1(X1) != iProver_top
% 7.47/1.51      | v1_xboole_0(X2) = iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_6498]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6505,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 7.47/1.51      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.47/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | v1_funct_1(sK5) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_4003,c_6499]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_44,plain,
% 7.47/1.51      ( v1_xboole_0(sK3) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_33,negated_conjecture,
% 7.47/1.51      ( v1_funct_2(sK5,sK3,sK2) ),
% 7.47/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_50,plain,
% 7.47/1.51      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_51,plain,
% 7.47/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6985,plain,
% 7.47/1.51      ( v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_6505,c_44,c_49,c_50,c_51]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6986,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_6985]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6992,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6591,c_6986]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6993,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_6992,c_3142]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6994,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_6993,c_6591]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6995,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_6994,c_3142]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6999,plain,
% 7.47/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 7.47/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 7.47/1.51      | v1_xboole_0(sK1)
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 7.47/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.47/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_6995]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_24,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.47/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_226,plain,
% 7.47/1.51      ( ~ v1_funct_1(X3)
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_24,c_27,c_26,c_25]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_227,plain,
% 7.47/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.47/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.47/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.47/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.47/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.47/1.51      | ~ v1_funct_1(X0)
% 7.47/1.51      | ~ v1_funct_1(X3)
% 7.47/1.51      | v1_xboole_0(X1)
% 7.47/1.51      | v1_xboole_0(X2)
% 7.47/1.51      | v1_xboole_0(X4)
% 7.47/1.51      | v1_xboole_0(X5)
% 7.47/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_226]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2130,plain,
% 7.47/1.51      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 7.47/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.47/1.51      | v1_funct_2(X5,X4,X1) != iProver_top
% 7.47/1.51      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 7.47/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.47/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 7.47/1.51      | v1_funct_1(X2) != iProver_top
% 7.47/1.51      | v1_funct_1(X5) != iProver_top
% 7.47/1.51      | v1_xboole_0(X3) = iProver_top
% 7.47/1.51      | v1_xboole_0(X1) = iProver_top
% 7.47/1.51      | v1_xboole_0(X4) = iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_227]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_6550,plain,
% 7.47/1.51      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 7.47/1.51      | v1_funct_2(X1,X0,sK2) != iProver_top
% 7.47/1.51      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | v1_funct_1(X1) != iProver_top
% 7.47/1.51      | v1_funct_1(sK6) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(X2) = iProver_top
% 7.47/1.51      | v1_xboole_0(sK2) = iProver_top
% 7.47/1.51      | v1_xboole_0(sK4) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3978,c_2130]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7482,plain,
% 7.47/1.51      ( v1_funct_1(X1) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | v1_funct_2(X1,X0,sK2) != iProver_top
% 7.47/1.51      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 7.47/1.51      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(X2) = iProver_top ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_6550,c_43,c_46,c_52,c_53,c_54]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7483,plain,
% 7.47/1.51      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,X0,sK4)) != k7_relat_1(sK6,k9_subset_1(X2,X0,sK4))
% 7.47/1.51      | k2_partfun1(k4_subset_1(X2,X0,sK4),sK2,k1_tmap_1(X2,sK2,X0,sK4,X1,sK6),X0) = X1
% 7.47/1.51      | v1_funct_2(X1,X0,sK2) != iProver_top
% 7.47/1.51      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X2)) != iProver_top
% 7.47/1.51      | v1_funct_1(X1) != iProver_top
% 7.47/1.51      | v1_xboole_0(X2) = iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_7482]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7489,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 7.47/1.51      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 7.47/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | v1_funct_1(sK5) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_4003,c_7483]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7671,plain,
% 7.47/1.51      ( v1_xboole_0(X0) = iProver_top
% 7.47/1.51      | k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_7489,c_44,c_49,c_50,c_51]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7672,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4))
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 7.47/1.51      | v1_xboole_0(X0) = iProver_top ),
% 7.47/1.51      inference(renaming,[status(thm)],[c_7671]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7678,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k3_xboole_0(sK3,sK4))
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_6591,c_7672]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7679,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_7678,c_3142]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7680,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK5,k3_xboole_0(sK3,sK4)) != k7_relat_1(sK6,k1_xboole_0)
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(demodulation,[status(thm)],[c_7679,c_6591]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7681,plain,
% 7.47/1.51      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.47/1.51      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.47/1.51      | v1_xboole_0(sK1) = iProver_top ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_7680,c_3142]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7685,plain,
% 7.47/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(sK1))
% 7.47/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 7.47/1.51      | v1_xboole_0(sK1)
% 7.47/1.51      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 7.47/1.51      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.47/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_7681]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8251,plain,
% 7.47/1.51      ( k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.47/1.51      inference(global_propositional_subsumption,
% 7.47/1.51                [status(thm)],
% 7.47/1.51                [c_6737,c_41,c_38,c_36,c_6999,c_7685]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_20,plain,
% 7.47/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.47/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2148,plain,
% 7.47/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.47/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3459,plain,
% 7.47/1.51      ( v1_relat_1(sK6) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2142,c_2148]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f99]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2152,plain,
% 7.47/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_14,plain,
% 7.47/1.51      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 7.47/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_17,plain,
% 7.47/1.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_542,plain,
% 7.47/1.51      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.47/1.51      | ~ v1_relat_1(X0)
% 7.47/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.47/1.51      inference(resolution,[status(thm)],[c_14,c_17]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2125,plain,
% 7.47/1.51      ( k7_relat_1(X0,X1) = X0
% 7.47/1.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.47/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_542]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7954,plain,
% 7.47/1.51      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2152,c_2125]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7959,plain,
% 7.47/1.51      ( k7_relat_1(sK6,k1_relat_1(sK6)) = sK6 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3459,c_7954]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2,plain,
% 7.47/1.51      ( v1_xboole_0(k1_xboole_0) ),
% 7.47/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2157,plain,
% 7.47/1.51      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_4,plain,
% 7.47/1.51      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2155,plain,
% 7.47/1.51      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 7.47/1.51      | r1_xboole_0(X0,X1) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_13,plain,
% 7.47/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.47/1.51      | ~ r2_hidden(X2,X0)
% 7.47/1.51      | ~ v1_xboole_0(X1) ),
% 7.47/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_402,plain,
% 7.47/1.51      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 7.47/1.51      inference(bin_hyper_res,[status(thm)],[c_13,c_315]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2126,plain,
% 7.47/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.47/1.51      | r2_hidden(X2,X0) != iProver_top
% 7.47/1.51      | v1_xboole_0(X1) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3455,plain,
% 7.47/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.47/1.51      | r1_xboole_0(X2,X0) = iProver_top
% 7.47/1.51      | v1_xboole_0(X1) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2155,c_2126]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7105,plain,
% 7.47/1.51      ( r1_xboole_0(X0,X1) = iProver_top | v1_xboole_0(X1) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2152,c_3455]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7216,plain,
% 7.47/1.51      ( k3_xboole_0(X0,X1) = k1_xboole_0 | v1_xboole_0(X1) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7105,c_2158]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7557,plain,
% 7.47/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2157,c_7216]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_0,plain,
% 7.47/1.51      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2159,plain,
% 7.47/1.51      ( k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1) = iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7559,plain,
% 7.47/1.51      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7557,c_2159]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_16,plain,
% 7.47/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.47/1.51      | ~ v1_relat_1(X2)
% 7.47/1.51      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.47/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_2149,plain,
% 7.47/1.51      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 7.47/1.51      | r1_xboole_0(X1,X2) != iProver_top
% 7.47/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.47/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7595,plain,
% 7.47/1.51      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 7.47/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7559,c_2149]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7913,plain,
% 7.47/1.51      ( k7_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3459,c_7595]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8032,plain,
% 7.47/1.51      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7959,c_7913]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_3460,plain,
% 7.47/1.51      ( v1_relat_1(sK5) = iProver_top ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_2139,c_2148]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7960,plain,
% 7.47/1.51      ( k7_relat_1(sK5,k1_relat_1(sK5)) = sK5 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3460,c_7954]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_7914,plain,
% 7.47/1.51      ( k7_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_3460,c_7595]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8065,plain,
% 7.47/1.51      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.47/1.51      inference(superposition,[status(thm)],[c_7960,c_7914]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8253,plain,
% 7.47/1.51      ( k1_xboole_0 != k1_xboole_0 ),
% 7.47/1.51      inference(light_normalisation,[status(thm)],[c_8251,c_8032,c_8065]) ).
% 7.47/1.51  
% 7.47/1.51  cnf(c_8254,plain,
% 7.47/1.51      ( $false ),
% 7.47/1.51      inference(equality_resolution_simp,[status(thm)],[c_8253]) ).
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.47/1.51  
% 7.47/1.51  ------                               Statistics
% 7.47/1.51  
% 7.47/1.51  ------ General
% 7.47/1.51  
% 7.47/1.51  abstr_ref_over_cycles:                  0
% 7.47/1.51  abstr_ref_under_cycles:                 0
% 7.47/1.51  gc_basic_clause_elim:                   0
% 7.47/1.51  forced_gc_time:                         0
% 7.47/1.51  parsing_time:                           0.01
% 7.47/1.51  unif_index_cands_time:                  0.
% 7.47/1.51  unif_index_add_time:                    0.
% 7.47/1.51  orderings_time:                         0.
% 7.47/1.51  out_proof_time:                         0.024
% 7.47/1.51  total_time:                             0.636
% 7.47/1.51  num_of_symbols:                         58
% 7.47/1.51  num_of_terms:                           17838
% 7.47/1.51  
% 7.47/1.51  ------ Preprocessing
% 7.47/1.51  
% 7.47/1.51  num_of_splits:                          0
% 7.47/1.51  num_of_split_atoms:                     0
% 7.47/1.51  num_of_reused_defs:                     0
% 7.47/1.51  num_eq_ax_congr_red:                    31
% 7.47/1.51  num_of_sem_filtered_clauses:            1
% 7.47/1.51  num_of_subtypes:                        0
% 7.47/1.51  monotx_restored_types:                  0
% 7.47/1.51  sat_num_of_epr_types:                   0
% 7.47/1.51  sat_num_of_non_cyclic_types:            0
% 7.47/1.51  sat_guarded_non_collapsed_types:        0
% 7.47/1.51  num_pure_diseq_elim:                    0
% 7.47/1.51  simp_replaced_by:                       0
% 7.47/1.51  res_preprocessed:                       185
% 7.47/1.51  prep_upred:                             0
% 7.47/1.51  prep_unflattend:                        28
% 7.47/1.51  smt_new_axioms:                         0
% 7.47/1.51  pred_elim_cands:                        8
% 7.47/1.51  pred_elim:                              2
% 7.47/1.51  pred_elim_cl:                           4
% 7.47/1.51  pred_elim_cycles:                       6
% 7.47/1.51  merged_defs:                            16
% 7.47/1.51  merged_defs_ncl:                        0
% 7.47/1.51  bin_hyper_res:                          19
% 7.47/1.51  prep_cycles:                            4
% 7.47/1.51  pred_elim_time:                         0.008
% 7.47/1.51  splitting_time:                         0.
% 7.47/1.51  sem_filter_time:                        0.
% 7.47/1.51  monotx_time:                            0.001
% 7.47/1.51  subtype_inf_time:                       0.
% 7.47/1.51  
% 7.47/1.51  ------ Problem properties
% 7.47/1.51  
% 7.47/1.51  clauses:                                37
% 7.47/1.51  conjectures:                            13
% 7.47/1.51  epr:                                    15
% 7.47/1.51  horn:                                   29
% 7.47/1.51  ground:                                 15
% 7.47/1.51  unary:                                  15
% 7.47/1.51  binary:                                 8
% 7.47/1.51  lits:                                   139
% 7.47/1.51  lits_eq:                                16
% 7.47/1.51  fd_pure:                                0
% 7.47/1.51  fd_pseudo:                              0
% 7.47/1.51  fd_cond:                                0
% 7.47/1.51  fd_pseudo_cond:                         1
% 7.47/1.51  ac_symbols:                             0
% 7.47/1.51  
% 7.47/1.51  ------ Propositional Solver
% 7.47/1.51  
% 7.47/1.51  prop_solver_calls:                      28
% 7.47/1.51  prop_fast_solver_calls:                 2018
% 7.47/1.51  smt_solver_calls:                       0
% 7.47/1.51  smt_fast_solver_calls:                  0
% 7.47/1.51  prop_num_of_clauses:                    3772
% 7.47/1.51  prop_preprocess_simplified:             10350
% 7.47/1.51  prop_fo_subsumed:                       78
% 7.47/1.51  prop_solver_time:                       0.
% 7.47/1.51  smt_solver_time:                        0.
% 7.47/1.51  smt_fast_solver_time:                   0.
% 7.47/1.51  prop_fast_solver_time:                  0.
% 7.47/1.51  prop_unsat_core_time:                   0.
% 7.47/1.51  
% 7.47/1.51  ------ QBF
% 7.47/1.51  
% 7.47/1.51  qbf_q_res:                              0
% 7.47/1.51  qbf_num_tautologies:                    0
% 7.47/1.51  qbf_prep_cycles:                        0
% 7.47/1.51  
% 7.47/1.51  ------ BMC1
% 7.47/1.51  
% 7.47/1.51  bmc1_current_bound:                     -1
% 7.47/1.51  bmc1_last_solved_bound:                 -1
% 7.47/1.51  bmc1_unsat_core_size:                   -1
% 7.47/1.51  bmc1_unsat_core_parents_size:           -1
% 7.47/1.51  bmc1_merge_next_fun:                    0
% 7.47/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.47/1.51  
% 7.47/1.51  ------ Instantiation
% 7.47/1.51  
% 7.47/1.51  inst_num_of_clauses:                    906
% 7.47/1.51  inst_num_in_passive:                    131
% 7.47/1.51  inst_num_in_active:                     499
% 7.47/1.51  inst_num_in_unprocessed:                276
% 7.47/1.51  inst_num_of_loops:                      580
% 7.47/1.51  inst_num_of_learning_restarts:          0
% 7.47/1.51  inst_num_moves_active_passive:          80
% 7.47/1.51  inst_lit_activity:                      0
% 7.47/1.51  inst_lit_activity_moves:                1
% 7.47/1.51  inst_num_tautologies:                   0
% 7.47/1.51  inst_num_prop_implied:                  0
% 7.47/1.51  inst_num_existing_simplified:           0
% 7.47/1.51  inst_num_eq_res_simplified:             0
% 7.47/1.51  inst_num_child_elim:                    0
% 7.47/1.51  inst_num_of_dismatching_blockings:      101
% 7.47/1.51  inst_num_of_non_proper_insts:           1053
% 7.47/1.51  inst_num_of_duplicates:                 0
% 7.47/1.51  inst_inst_num_from_inst_to_res:         0
% 7.47/1.51  inst_dismatching_checking_time:         0.
% 7.47/1.51  
% 7.47/1.51  ------ Resolution
% 7.47/1.51  
% 7.47/1.51  res_num_of_clauses:                     0
% 7.47/1.51  res_num_in_passive:                     0
% 7.47/1.51  res_num_in_active:                      0
% 7.47/1.51  res_num_of_loops:                       189
% 7.47/1.51  res_forward_subset_subsumed:            23
% 7.47/1.51  res_backward_subset_subsumed:           0
% 7.47/1.51  res_forward_subsumed:                   0
% 7.47/1.51  res_backward_subsumed:                  0
% 7.47/1.51  res_forward_subsumption_resolution:     0
% 7.47/1.51  res_backward_subsumption_resolution:    0
% 7.47/1.51  res_clause_to_clause_subsumption:       490
% 7.47/1.51  res_orphan_elimination:                 0
% 7.47/1.51  res_tautology_del:                      49
% 7.47/1.51  res_num_eq_res_simplified:              0
% 7.47/1.51  res_num_sel_changes:                    0
% 7.47/1.51  res_moves_from_active_to_pass:          0
% 7.47/1.51  
% 7.47/1.51  ------ Superposition
% 7.47/1.51  
% 7.47/1.51  sup_time_total:                         0.
% 7.47/1.51  sup_time_generating:                    0.
% 7.47/1.51  sup_time_sim_full:                      0.
% 7.47/1.51  sup_time_sim_immed:                     0.
% 7.47/1.51  
% 7.47/1.51  sup_num_of_clauses:                     181
% 7.47/1.51  sup_num_in_active:                      110
% 7.47/1.51  sup_num_in_passive:                     71
% 7.47/1.51  sup_num_of_loops:                       115
% 7.47/1.51  sup_fw_superposition:                   137
% 7.47/1.51  sup_bw_superposition:                   56
% 7.47/1.51  sup_immediate_simplified:               81
% 7.47/1.51  sup_given_eliminated:                   0
% 7.47/1.51  comparisons_done:                       0
% 7.47/1.51  comparisons_avoided:                    0
% 7.47/1.51  
% 7.47/1.51  ------ Simplifications
% 7.47/1.51  
% 7.47/1.51  
% 7.47/1.51  sim_fw_subset_subsumed:                 6
% 7.47/1.51  sim_bw_subset_subsumed:                 0
% 7.47/1.51  sim_fw_subsumed:                        7
% 7.47/1.51  sim_bw_subsumed:                        2
% 7.47/1.51  sim_fw_subsumption_res:                 0
% 7.47/1.51  sim_bw_subsumption_res:                 0
% 7.47/1.51  sim_tautology_del:                      3
% 7.47/1.51  sim_eq_tautology_del:                   1
% 7.47/1.51  sim_eq_res_simp:                        0
% 7.47/1.51  sim_fw_demodulated:                     46
% 7.47/1.51  sim_bw_demodulated:                     5
% 7.47/1.51  sim_light_normalised:                   34
% 7.47/1.51  sim_joinable_taut:                      0
% 7.47/1.51  sim_joinable_simp:                      0
% 7.47/1.51  sim_ac_normalised:                      0
% 7.47/1.51  sim_smt_subsumption:                    0
% 7.47/1.51  
%------------------------------------------------------------------------------
