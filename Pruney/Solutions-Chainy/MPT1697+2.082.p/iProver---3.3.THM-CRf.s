%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:41 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.38s
% Verified   : 
% Statistics : Number of formulae       :  219 (3441 expanded)
%              Number of clauses        :  156 ( 899 expanded)
%              Number of leaves         :   16 (1359 expanded)
%              Depth                    :   25
%              Number of atoms          : 1297 (45472 expanded)
%              Number of equality atoms :  608 (10860 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f34,f33,f32,f31,f30,f29])).

fof(f63,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f64,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
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
    inference(equality_resolution,[],[f45])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
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
    inference(equality_resolution,[],[f46])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_568,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1022,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_568])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | ~ v1_relat_1(X1_50)
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1014,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_2128,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1014])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | v1_relat_1(X0_50)
    | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_1523,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1522])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_576,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2219,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_2220,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2219])).

cnf(c_2440,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2128,c_41,c_1523,c_2220])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_575,plain,
    ( ~ v1_relat_1(X0_50)
    | k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1016,plain,
    ( k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_2445,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2440,c_1016])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_562,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1028,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | k9_subset_1(X1_50,X2_50,X0_50) = k3_xboole_0(X2_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1013,plain,
    ( k9_subset_1(X0_50,X1_50,X2_50) = k3_xboole_0(X1_50,X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_1802,plain,
    ( k9_subset_1(sK0,X0_50,sK3) = k3_xboole_0(X0_50,sK3) ),
    inference(superposition,[status(thm)],[c_1028,c_1013])).

cnf(c_15,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_569,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2074,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1802,c_569])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_211,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_378,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_379,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_381,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_26,c_24])).

cnf(c_392,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_211,c_381])).

cnf(c_393,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_554,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_2075,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2074,c_554])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | k2_partfun1(X1_50,X2_50,X0_50,X3_50) = k7_relat_1(X0_50,X3_50) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1017,plain,
    ( k2_partfun1(X0_50,X1_50,X2_50,X3_50) = k7_relat_1(X2_50,X3_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_2189,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_1017])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_50,X1_50,sK5,X2_50) = k7_relat_1(sK5,X2_50) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1528,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_2529,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2189,c_18,c_16,c_1528])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_565,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1025,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_2190,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1017])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1390,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_50,X1_50,sK4,X2_50) = k7_relat_1(sK4,X2_50) ),
    inference(instantiation,[status(thm)],[c_574])).

cnf(c_1533,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_2597,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2190,c_21,c_19,c_1533])).

cnf(c_2601,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2075,c_2529,c_2597])).

cnf(c_2961,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2445,c_2601])).

cnf(c_1525,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1319])).

cnf(c_1784,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_2223,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_14889,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2961,c_19,c_1525,c_1784,c_2223])).

cnf(c_14890,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_14889])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f50])).

cnf(c_572,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1019,plain,
    ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
    | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_xboole_0(X5_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_2264,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
    | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
    | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_1017])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_570,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50))
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1021,plain,
    ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
    | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50)) = iProver_top
    | v1_xboole_0(X5_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_6514,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
    | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
    | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2264,c_1021])).

cnf(c_6518,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
    | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1022,c_6514])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_33,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_39,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_40,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6625,plain,
    ( v1_funct_1(X2_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
    | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6518,c_30,c_33,c_39,c_40])).

cnf(c_6626,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
    | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_6625])).

cnf(c_6640,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_6626])).

cnf(c_31,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_37,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7233,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6640,c_31,c_36,c_37])).

cnf(c_7234,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_7233])).

cnf(c_7243,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1028,c_7234])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7248,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7243,c_29,c_32])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_156,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_14,c_13,c_12])).

cnf(c_157,plain,
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
    inference(renaming,[status(thm)],[c_156])).

cnf(c_556,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50)
    | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
    | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X4_50) = X3_50 ),
    inference(subtyping,[status(esa)],[c_157])).

cnf(c_1034,plain,
    ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
    | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X4_50) = X5_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_4142,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2529,c_1034])).

cnf(c_10050,plain,
    ( v1_funct_1(X1_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4142,c_30,c_33,c_39,c_40,c_41])).

cnf(c_10051,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_10050])).

cnf(c_10071,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_10051])).

cnf(c_10081,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10071,c_1802])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10342,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10081,c_29,c_34])).

cnf(c_10343,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_10342])).

cnf(c_10356,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_10343])).

cnf(c_2129,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1025,c_1014])).

cnf(c_38,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1526,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_2224,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2223])).

cnf(c_2522,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_38,c_1526,c_2224])).

cnf(c_2527,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2522,c_1016])).

cnf(c_10440,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10356,c_554,c_2445,c_2527])).

cnf(c_10441,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10440])).

cnf(c_10442,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10441,c_7248])).

cnf(c_10066,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_10051])).

cnf(c_10276,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10066,c_31,c_36,c_37,c_38])).

cnf(c_10277,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_10276])).

cnf(c_10287,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_10277])).

cnf(c_10288,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10287,c_554,c_2445])).

cnf(c_10289,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10288,c_1802,c_7248])).

cnf(c_10290,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10289,c_554,c_2527])).

cnf(c_10291,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10290])).

cnf(c_10465,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10442,c_29,c_32,c_34,c_10291])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_163,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_14,c_13,c_12])).

cnf(c_164,plain,
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
    inference(renaming,[status(thm)],[c_163])).

cnf(c_555,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50)
    | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
    | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X1_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_164])).

cnf(c_1035,plain,
    ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
    | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X0_50) = X2_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_5712,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2529,c_1035])).

cnf(c_13496,plain,
    ( v1_funct_1(X1_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5712,c_30,c_33,c_39,c_40,c_41])).

cnf(c_13497,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_13496])).

cnf(c_13517,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_13497])).

cnf(c_13527,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13517,c_1802])).

cnf(c_13694,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13527,c_29,c_34])).

cnf(c_13695,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_13694])).

cnf(c_13708,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_13695])).

cnf(c_13792,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13708,c_554,c_2445,c_2527])).

cnf(c_13793,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13792])).

cnf(c_13794,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13793,c_7248])).

cnf(c_13512,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_13497])).

cnf(c_13676,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13512,c_31,c_36,c_37,c_38])).

cnf(c_13677,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_13676])).

cnf(c_13687,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_13677])).

cnf(c_13688,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13687,c_554,c_2445])).

cnf(c_13689,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13688,c_1802,c_7248])).

cnf(c_13690,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13689,c_554,c_2527])).

cnf(c_13691,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13690])).

cnf(c_13860,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13794,c_29,c_32,c_34,c_13691])).

cnf(c_14891,plain,
    ( sK5 != sK5
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_14890,c_7248,c_10465,c_13860])).

cnf(c_14892,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14891])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:56:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 6.38/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/1.50  
% 6.38/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.38/1.50  
% 6.38/1.50  ------  iProver source info
% 6.38/1.50  
% 6.38/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.38/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.38/1.50  git: non_committed_changes: false
% 6.38/1.50  git: last_make_outside_of_git: false
% 6.38/1.50  
% 6.38/1.50  ------ 
% 6.38/1.50  
% 6.38/1.50  ------ Input Options
% 6.38/1.50  
% 6.38/1.50  --out_options                           all
% 6.38/1.50  --tptp_safe_out                         true
% 6.38/1.50  --problem_path                          ""
% 6.38/1.50  --include_path                          ""
% 6.38/1.50  --clausifier                            res/vclausify_rel
% 6.38/1.50  --clausifier_options                    --mode clausify
% 6.38/1.50  --stdin                                 false
% 6.38/1.50  --stats_out                             all
% 6.38/1.50  
% 6.38/1.50  ------ General Options
% 6.38/1.50  
% 6.38/1.50  --fof                                   false
% 6.38/1.50  --time_out_real                         305.
% 6.38/1.50  --time_out_virtual                      -1.
% 6.38/1.50  --symbol_type_check                     false
% 6.38/1.50  --clausify_out                          false
% 6.38/1.50  --sig_cnt_out                           false
% 6.38/1.50  --trig_cnt_out                          false
% 6.38/1.50  --trig_cnt_out_tolerance                1.
% 6.38/1.50  --trig_cnt_out_sk_spl                   false
% 6.38/1.50  --abstr_cl_out                          false
% 6.38/1.50  
% 6.38/1.50  ------ Global Options
% 6.38/1.50  
% 6.38/1.50  --schedule                              default
% 6.38/1.50  --add_important_lit                     false
% 6.38/1.50  --prop_solver_per_cl                    1000
% 6.38/1.50  --min_unsat_core                        false
% 6.38/1.50  --soft_assumptions                      false
% 6.38/1.50  --soft_lemma_size                       3
% 6.38/1.50  --prop_impl_unit_size                   0
% 6.38/1.50  --prop_impl_unit                        []
% 6.38/1.50  --share_sel_clauses                     true
% 6.38/1.50  --reset_solvers                         false
% 6.38/1.50  --bc_imp_inh                            [conj_cone]
% 6.38/1.50  --conj_cone_tolerance                   3.
% 6.38/1.50  --extra_neg_conj                        none
% 6.38/1.50  --large_theory_mode                     true
% 6.38/1.50  --prolific_symb_bound                   200
% 6.38/1.50  --lt_threshold                          2000
% 6.38/1.50  --clause_weak_htbl                      true
% 6.38/1.50  --gc_record_bc_elim                     false
% 6.38/1.50  
% 6.38/1.50  ------ Preprocessing Options
% 6.38/1.50  
% 6.38/1.50  --preprocessing_flag                    true
% 6.38/1.50  --time_out_prep_mult                    0.1
% 6.38/1.50  --splitting_mode                        input
% 6.38/1.50  --splitting_grd                         true
% 6.38/1.50  --splitting_cvd                         false
% 6.38/1.50  --splitting_cvd_svl                     false
% 6.38/1.50  --splitting_nvd                         32
% 6.38/1.50  --sub_typing                            true
% 6.38/1.50  --prep_gs_sim                           true
% 6.38/1.50  --prep_unflatten                        true
% 6.38/1.50  --prep_res_sim                          true
% 6.38/1.50  --prep_upred                            true
% 6.38/1.50  --prep_sem_filter                       exhaustive
% 6.38/1.50  --prep_sem_filter_out                   false
% 6.38/1.50  --pred_elim                             true
% 6.38/1.50  --res_sim_input                         true
% 6.38/1.50  --eq_ax_congr_red                       true
% 6.38/1.50  --pure_diseq_elim                       true
% 6.38/1.50  --brand_transform                       false
% 6.38/1.50  --non_eq_to_eq                          false
% 6.38/1.50  --prep_def_merge                        true
% 6.38/1.50  --prep_def_merge_prop_impl              false
% 6.38/1.50  --prep_def_merge_mbd                    true
% 6.38/1.50  --prep_def_merge_tr_red                 false
% 6.38/1.50  --prep_def_merge_tr_cl                  false
% 6.38/1.50  --smt_preprocessing                     true
% 6.38/1.50  --smt_ac_axioms                         fast
% 6.38/1.50  --preprocessed_out                      false
% 6.38/1.50  --preprocessed_stats                    false
% 6.38/1.50  
% 6.38/1.50  ------ Abstraction refinement Options
% 6.38/1.50  
% 6.38/1.50  --abstr_ref                             []
% 6.38/1.50  --abstr_ref_prep                        false
% 6.38/1.50  --abstr_ref_until_sat                   false
% 6.38/1.50  --abstr_ref_sig_restrict                funpre
% 6.38/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.38/1.50  --abstr_ref_under                       []
% 6.38/1.50  
% 6.38/1.50  ------ SAT Options
% 6.38/1.50  
% 6.38/1.50  --sat_mode                              false
% 6.38/1.50  --sat_fm_restart_options                ""
% 6.38/1.50  --sat_gr_def                            false
% 6.38/1.50  --sat_epr_types                         true
% 6.38/1.50  --sat_non_cyclic_types                  false
% 6.38/1.50  --sat_finite_models                     false
% 6.38/1.50  --sat_fm_lemmas                         false
% 6.38/1.50  --sat_fm_prep                           false
% 6.38/1.50  --sat_fm_uc_incr                        true
% 6.38/1.50  --sat_out_model                         small
% 6.38/1.50  --sat_out_clauses                       false
% 6.38/1.50  
% 6.38/1.50  ------ QBF Options
% 6.38/1.50  
% 6.38/1.50  --qbf_mode                              false
% 6.38/1.50  --qbf_elim_univ                         false
% 6.38/1.50  --qbf_dom_inst                          none
% 6.38/1.50  --qbf_dom_pre_inst                      false
% 6.38/1.50  --qbf_sk_in                             false
% 6.38/1.50  --qbf_pred_elim                         true
% 6.38/1.50  --qbf_split                             512
% 6.38/1.50  
% 6.38/1.50  ------ BMC1 Options
% 6.38/1.50  
% 6.38/1.50  --bmc1_incremental                      false
% 6.38/1.50  --bmc1_axioms                           reachable_all
% 6.38/1.50  --bmc1_min_bound                        0
% 6.38/1.50  --bmc1_max_bound                        -1
% 6.38/1.50  --bmc1_max_bound_default                -1
% 6.38/1.50  --bmc1_symbol_reachability              true
% 6.38/1.50  --bmc1_property_lemmas                  false
% 6.38/1.50  --bmc1_k_induction                      false
% 6.38/1.50  --bmc1_non_equiv_states                 false
% 6.38/1.50  --bmc1_deadlock                         false
% 6.38/1.50  --bmc1_ucm                              false
% 6.38/1.50  --bmc1_add_unsat_core                   none
% 6.38/1.50  --bmc1_unsat_core_children              false
% 6.38/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.38/1.50  --bmc1_out_stat                         full
% 6.38/1.50  --bmc1_ground_init                      false
% 6.38/1.50  --bmc1_pre_inst_next_state              false
% 6.38/1.50  --bmc1_pre_inst_state                   false
% 6.38/1.50  --bmc1_pre_inst_reach_state             false
% 6.38/1.50  --bmc1_out_unsat_core                   false
% 6.38/1.50  --bmc1_aig_witness_out                  false
% 6.38/1.50  --bmc1_verbose                          false
% 6.38/1.50  --bmc1_dump_clauses_tptp                false
% 6.38/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.38/1.50  --bmc1_dump_file                        -
% 6.38/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.38/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.38/1.50  --bmc1_ucm_extend_mode                  1
% 6.38/1.50  --bmc1_ucm_init_mode                    2
% 6.38/1.50  --bmc1_ucm_cone_mode                    none
% 6.38/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.38/1.50  --bmc1_ucm_relax_model                  4
% 6.38/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.38/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.38/1.50  --bmc1_ucm_layered_model                none
% 6.38/1.50  --bmc1_ucm_max_lemma_size               10
% 6.38/1.50  
% 6.38/1.50  ------ AIG Options
% 6.38/1.50  
% 6.38/1.50  --aig_mode                              false
% 6.38/1.50  
% 6.38/1.50  ------ Instantiation Options
% 6.38/1.50  
% 6.38/1.50  --instantiation_flag                    true
% 6.38/1.50  --inst_sos_flag                         false
% 6.38/1.50  --inst_sos_phase                        true
% 6.38/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.38/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.38/1.50  --inst_lit_sel_side                     num_symb
% 6.38/1.50  --inst_solver_per_active                1400
% 6.38/1.50  --inst_solver_calls_frac                1.
% 6.38/1.50  --inst_passive_queue_type               priority_queues
% 6.38/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.38/1.50  --inst_passive_queues_freq              [25;2]
% 6.38/1.50  --inst_dismatching                      true
% 6.38/1.50  --inst_eager_unprocessed_to_passive     true
% 6.38/1.50  --inst_prop_sim_given                   true
% 6.38/1.50  --inst_prop_sim_new                     false
% 6.38/1.50  --inst_subs_new                         false
% 6.38/1.50  --inst_eq_res_simp                      false
% 6.38/1.50  --inst_subs_given                       false
% 6.38/1.50  --inst_orphan_elimination               true
% 6.38/1.50  --inst_learning_loop_flag               true
% 6.38/1.50  --inst_learning_start                   3000
% 6.38/1.50  --inst_learning_factor                  2
% 6.38/1.50  --inst_start_prop_sim_after_learn       3
% 6.38/1.50  --inst_sel_renew                        solver
% 6.38/1.50  --inst_lit_activity_flag                true
% 6.38/1.50  --inst_restr_to_given                   false
% 6.38/1.50  --inst_activity_threshold               500
% 6.38/1.50  --inst_out_proof                        true
% 6.38/1.50  
% 6.38/1.50  ------ Resolution Options
% 6.38/1.50  
% 6.38/1.50  --resolution_flag                       true
% 6.38/1.50  --res_lit_sel                           adaptive
% 6.38/1.50  --res_lit_sel_side                      none
% 6.38/1.50  --res_ordering                          kbo
% 6.38/1.50  --res_to_prop_solver                    active
% 6.38/1.50  --res_prop_simpl_new                    false
% 6.38/1.50  --res_prop_simpl_given                  true
% 6.38/1.50  --res_passive_queue_type                priority_queues
% 6.38/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.38/1.50  --res_passive_queues_freq               [15;5]
% 6.38/1.50  --res_forward_subs                      full
% 6.38/1.50  --res_backward_subs                     full
% 6.38/1.50  --res_forward_subs_resolution           true
% 6.38/1.50  --res_backward_subs_resolution          true
% 6.38/1.50  --res_orphan_elimination                true
% 6.38/1.50  --res_time_limit                        2.
% 6.38/1.50  --res_out_proof                         true
% 6.38/1.50  
% 6.38/1.50  ------ Superposition Options
% 6.38/1.50  
% 6.38/1.50  --superposition_flag                    true
% 6.38/1.50  --sup_passive_queue_type                priority_queues
% 6.38/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.38/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.38/1.50  --demod_completeness_check              fast
% 6.38/1.50  --demod_use_ground                      true
% 6.38/1.50  --sup_to_prop_solver                    passive
% 6.38/1.50  --sup_prop_simpl_new                    true
% 6.38/1.50  --sup_prop_simpl_given                  true
% 6.38/1.50  --sup_fun_splitting                     false
% 6.38/1.50  --sup_smt_interval                      50000
% 6.38/1.50  
% 6.38/1.50  ------ Superposition Simplification Setup
% 6.38/1.50  
% 6.38/1.50  --sup_indices_passive                   []
% 6.38/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.38/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.38/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.38/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.38/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.38/1.50  --sup_full_bw                           [BwDemod]
% 6.38/1.50  --sup_immed_triv                        [TrivRules]
% 6.38/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.38/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.38/1.50  --sup_immed_bw_main                     []
% 6.38/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.38/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.38/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.38/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.38/1.50  
% 6.38/1.50  ------ Combination Options
% 6.38/1.50  
% 6.38/1.50  --comb_res_mult                         3
% 6.38/1.50  --comb_sup_mult                         2
% 6.38/1.50  --comb_inst_mult                        10
% 6.38/1.50  
% 6.38/1.50  ------ Debug Options
% 6.38/1.50  
% 6.38/1.50  --dbg_backtrace                         false
% 6.38/1.50  --dbg_dump_prop_clauses                 false
% 6.38/1.50  --dbg_dump_prop_clauses_file            -
% 6.38/1.50  --dbg_out_stat                          false
% 6.38/1.50  ------ Parsing...
% 6.38/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.38/1.50  
% 6.38/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.38/1.50  
% 6.38/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.38/1.50  
% 6.38/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.38/1.50  ------ Proving...
% 6.38/1.50  ------ Problem Properties 
% 6.38/1.50  
% 6.38/1.50  
% 6.38/1.50  clauses                                 25
% 6.38/1.50  conjectures                             13
% 6.38/1.50  EPR                                     8
% 6.38/1.50  Horn                                    19
% 6.38/1.50  unary                                   14
% 6.38/1.50  binary                                  2
% 6.38/1.50  lits                                    111
% 6.38/1.50  lits eq                                 13
% 6.38/1.50  fd_pure                                 0
% 6.38/1.50  fd_pseudo                               0
% 6.38/1.50  fd_cond                                 0
% 6.38/1.50  fd_pseudo_cond                          0
% 6.38/1.50  AC symbols                              0
% 6.38/1.50  
% 6.38/1.50  ------ Schedule dynamic 5 is on 
% 6.38/1.50  
% 6.38/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.38/1.50  
% 6.38/1.50  
% 6.38/1.50  ------ 
% 6.38/1.50  Current options:
% 6.38/1.50  ------ 
% 6.38/1.50  
% 6.38/1.50  ------ Input Options
% 6.38/1.50  
% 6.38/1.50  --out_options                           all
% 6.38/1.50  --tptp_safe_out                         true
% 6.38/1.50  --problem_path                          ""
% 6.38/1.50  --include_path                          ""
% 6.38/1.50  --clausifier                            res/vclausify_rel
% 6.38/1.50  --clausifier_options                    --mode clausify
% 6.38/1.50  --stdin                                 false
% 6.38/1.50  --stats_out                             all
% 6.38/1.50  
% 6.38/1.50  ------ General Options
% 6.38/1.50  
% 6.38/1.50  --fof                                   false
% 6.38/1.50  --time_out_real                         305.
% 6.38/1.50  --time_out_virtual                      -1.
% 6.38/1.50  --symbol_type_check                     false
% 6.38/1.50  --clausify_out                          false
% 6.38/1.50  --sig_cnt_out                           false
% 6.38/1.50  --trig_cnt_out                          false
% 6.38/1.50  --trig_cnt_out_tolerance                1.
% 6.38/1.50  --trig_cnt_out_sk_spl                   false
% 6.38/1.50  --abstr_cl_out                          false
% 6.38/1.50  
% 6.38/1.50  ------ Global Options
% 6.38/1.50  
% 6.38/1.50  --schedule                              default
% 6.38/1.50  --add_important_lit                     false
% 6.38/1.50  --prop_solver_per_cl                    1000
% 6.38/1.50  --min_unsat_core                        false
% 6.38/1.50  --soft_assumptions                      false
% 6.38/1.50  --soft_lemma_size                       3
% 6.38/1.50  --prop_impl_unit_size                   0
% 6.38/1.50  --prop_impl_unit                        []
% 6.38/1.50  --share_sel_clauses                     true
% 6.38/1.50  --reset_solvers                         false
% 6.38/1.50  --bc_imp_inh                            [conj_cone]
% 6.38/1.50  --conj_cone_tolerance                   3.
% 6.38/1.50  --extra_neg_conj                        none
% 6.38/1.50  --large_theory_mode                     true
% 6.38/1.50  --prolific_symb_bound                   200
% 6.38/1.50  --lt_threshold                          2000
% 6.38/1.50  --clause_weak_htbl                      true
% 6.38/1.50  --gc_record_bc_elim                     false
% 6.38/1.50  
% 6.38/1.50  ------ Preprocessing Options
% 6.38/1.50  
% 6.38/1.50  --preprocessing_flag                    true
% 6.38/1.50  --time_out_prep_mult                    0.1
% 6.38/1.50  --splitting_mode                        input
% 6.38/1.50  --splitting_grd                         true
% 6.38/1.50  --splitting_cvd                         false
% 6.38/1.50  --splitting_cvd_svl                     false
% 6.38/1.50  --splitting_nvd                         32
% 6.38/1.50  --sub_typing                            true
% 6.38/1.50  --prep_gs_sim                           true
% 6.38/1.50  --prep_unflatten                        true
% 6.38/1.50  --prep_res_sim                          true
% 6.38/1.50  --prep_upred                            true
% 6.38/1.50  --prep_sem_filter                       exhaustive
% 6.38/1.50  --prep_sem_filter_out                   false
% 6.38/1.50  --pred_elim                             true
% 6.38/1.50  --res_sim_input                         true
% 6.38/1.50  --eq_ax_congr_red                       true
% 6.38/1.50  --pure_diseq_elim                       true
% 6.38/1.50  --brand_transform                       false
% 6.38/1.50  --non_eq_to_eq                          false
% 6.38/1.50  --prep_def_merge                        true
% 6.38/1.50  --prep_def_merge_prop_impl              false
% 6.38/1.50  --prep_def_merge_mbd                    true
% 6.38/1.50  --prep_def_merge_tr_red                 false
% 6.38/1.50  --prep_def_merge_tr_cl                  false
% 6.38/1.50  --smt_preprocessing                     true
% 6.38/1.50  --smt_ac_axioms                         fast
% 6.38/1.50  --preprocessed_out                      false
% 6.38/1.50  --preprocessed_stats                    false
% 6.38/1.50  
% 6.38/1.50  ------ Abstraction refinement Options
% 6.38/1.50  
% 6.38/1.50  --abstr_ref                             []
% 6.38/1.50  --abstr_ref_prep                        false
% 6.38/1.50  --abstr_ref_until_sat                   false
% 6.38/1.50  --abstr_ref_sig_restrict                funpre
% 6.38/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 6.38/1.50  --abstr_ref_under                       []
% 6.38/1.50  
% 6.38/1.50  ------ SAT Options
% 6.38/1.50  
% 6.38/1.50  --sat_mode                              false
% 6.38/1.50  --sat_fm_restart_options                ""
% 6.38/1.50  --sat_gr_def                            false
% 6.38/1.50  --sat_epr_types                         true
% 6.38/1.50  --sat_non_cyclic_types                  false
% 6.38/1.50  --sat_finite_models                     false
% 6.38/1.50  --sat_fm_lemmas                         false
% 6.38/1.50  --sat_fm_prep                           false
% 6.38/1.50  --sat_fm_uc_incr                        true
% 6.38/1.50  --sat_out_model                         small
% 6.38/1.50  --sat_out_clauses                       false
% 6.38/1.50  
% 6.38/1.50  ------ QBF Options
% 6.38/1.50  
% 6.38/1.50  --qbf_mode                              false
% 6.38/1.50  --qbf_elim_univ                         false
% 6.38/1.50  --qbf_dom_inst                          none
% 6.38/1.50  --qbf_dom_pre_inst                      false
% 6.38/1.50  --qbf_sk_in                             false
% 6.38/1.50  --qbf_pred_elim                         true
% 6.38/1.50  --qbf_split                             512
% 6.38/1.50  
% 6.38/1.50  ------ BMC1 Options
% 6.38/1.50  
% 6.38/1.50  --bmc1_incremental                      false
% 6.38/1.50  --bmc1_axioms                           reachable_all
% 6.38/1.50  --bmc1_min_bound                        0
% 6.38/1.50  --bmc1_max_bound                        -1
% 6.38/1.50  --bmc1_max_bound_default                -1
% 6.38/1.50  --bmc1_symbol_reachability              true
% 6.38/1.50  --bmc1_property_lemmas                  false
% 6.38/1.50  --bmc1_k_induction                      false
% 6.38/1.50  --bmc1_non_equiv_states                 false
% 6.38/1.50  --bmc1_deadlock                         false
% 6.38/1.50  --bmc1_ucm                              false
% 6.38/1.50  --bmc1_add_unsat_core                   none
% 6.38/1.50  --bmc1_unsat_core_children              false
% 6.38/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 6.38/1.50  --bmc1_out_stat                         full
% 6.38/1.50  --bmc1_ground_init                      false
% 6.38/1.50  --bmc1_pre_inst_next_state              false
% 6.38/1.50  --bmc1_pre_inst_state                   false
% 6.38/1.50  --bmc1_pre_inst_reach_state             false
% 6.38/1.50  --bmc1_out_unsat_core                   false
% 6.38/1.50  --bmc1_aig_witness_out                  false
% 6.38/1.50  --bmc1_verbose                          false
% 6.38/1.50  --bmc1_dump_clauses_tptp                false
% 6.38/1.50  --bmc1_dump_unsat_core_tptp             false
% 6.38/1.50  --bmc1_dump_file                        -
% 6.38/1.50  --bmc1_ucm_expand_uc_limit              128
% 6.38/1.50  --bmc1_ucm_n_expand_iterations          6
% 6.38/1.50  --bmc1_ucm_extend_mode                  1
% 6.38/1.50  --bmc1_ucm_init_mode                    2
% 6.38/1.50  --bmc1_ucm_cone_mode                    none
% 6.38/1.50  --bmc1_ucm_reduced_relation_type        0
% 6.38/1.50  --bmc1_ucm_relax_model                  4
% 6.38/1.50  --bmc1_ucm_full_tr_after_sat            true
% 6.38/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 6.38/1.50  --bmc1_ucm_layered_model                none
% 6.38/1.50  --bmc1_ucm_max_lemma_size               10
% 6.38/1.50  
% 6.38/1.50  ------ AIG Options
% 6.38/1.50  
% 6.38/1.50  --aig_mode                              false
% 6.38/1.50  
% 6.38/1.50  ------ Instantiation Options
% 6.38/1.50  
% 6.38/1.50  --instantiation_flag                    true
% 6.38/1.50  --inst_sos_flag                         false
% 6.38/1.50  --inst_sos_phase                        true
% 6.38/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.38/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.38/1.50  --inst_lit_sel_side                     none
% 6.38/1.50  --inst_solver_per_active                1400
% 6.38/1.50  --inst_solver_calls_frac                1.
% 6.38/1.50  --inst_passive_queue_type               priority_queues
% 6.38/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.38/1.50  --inst_passive_queues_freq              [25;2]
% 6.38/1.50  --inst_dismatching                      true
% 6.38/1.50  --inst_eager_unprocessed_to_passive     true
% 6.38/1.50  --inst_prop_sim_given                   true
% 6.38/1.50  --inst_prop_sim_new                     false
% 6.38/1.50  --inst_subs_new                         false
% 6.38/1.50  --inst_eq_res_simp                      false
% 6.38/1.50  --inst_subs_given                       false
% 6.38/1.50  --inst_orphan_elimination               true
% 6.38/1.50  --inst_learning_loop_flag               true
% 6.38/1.50  --inst_learning_start                   3000
% 6.38/1.50  --inst_learning_factor                  2
% 6.38/1.50  --inst_start_prop_sim_after_learn       3
% 6.38/1.50  --inst_sel_renew                        solver
% 6.38/1.50  --inst_lit_activity_flag                true
% 6.38/1.50  --inst_restr_to_given                   false
% 6.38/1.50  --inst_activity_threshold               500
% 6.38/1.50  --inst_out_proof                        true
% 6.38/1.50  
% 6.38/1.50  ------ Resolution Options
% 6.38/1.50  
% 6.38/1.50  --resolution_flag                       false
% 6.38/1.50  --res_lit_sel                           adaptive
% 6.38/1.50  --res_lit_sel_side                      none
% 6.38/1.50  --res_ordering                          kbo
% 6.38/1.50  --res_to_prop_solver                    active
% 6.38/1.50  --res_prop_simpl_new                    false
% 6.38/1.50  --res_prop_simpl_given                  true
% 6.38/1.50  --res_passive_queue_type                priority_queues
% 6.38/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.38/1.50  --res_passive_queues_freq               [15;5]
% 6.38/1.50  --res_forward_subs                      full
% 6.38/1.50  --res_backward_subs                     full
% 6.38/1.50  --res_forward_subs_resolution           true
% 6.38/1.50  --res_backward_subs_resolution          true
% 6.38/1.50  --res_orphan_elimination                true
% 6.38/1.50  --res_time_limit                        2.
% 6.38/1.50  --res_out_proof                         true
% 6.38/1.50  
% 6.38/1.50  ------ Superposition Options
% 6.38/1.50  
% 6.38/1.50  --superposition_flag                    true
% 6.38/1.50  --sup_passive_queue_type                priority_queues
% 6.38/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.38/1.50  --sup_passive_queues_freq               [8;1;4]
% 6.38/1.50  --demod_completeness_check              fast
% 6.38/1.50  --demod_use_ground                      true
% 6.38/1.50  --sup_to_prop_solver                    passive
% 6.38/1.50  --sup_prop_simpl_new                    true
% 6.38/1.50  --sup_prop_simpl_given                  true
% 6.38/1.50  --sup_fun_splitting                     false
% 6.38/1.50  --sup_smt_interval                      50000
% 6.38/1.50  
% 6.38/1.50  ------ Superposition Simplification Setup
% 6.38/1.50  
% 6.38/1.50  --sup_indices_passive                   []
% 6.38/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.38/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.38/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.38/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 6.38/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.38/1.50  --sup_full_bw                           [BwDemod]
% 6.38/1.50  --sup_immed_triv                        [TrivRules]
% 6.38/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.38/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.38/1.50  --sup_immed_bw_main                     []
% 6.38/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.38/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 6.38/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.38/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.38/1.50  
% 6.38/1.50  ------ Combination Options
% 6.38/1.50  
% 6.38/1.50  --comb_res_mult                         3
% 6.38/1.50  --comb_sup_mult                         2
% 6.38/1.50  --comb_inst_mult                        10
% 6.38/1.50  
% 6.38/1.50  ------ Debug Options
% 6.38/1.50  
% 6.38/1.50  --dbg_backtrace                         false
% 6.38/1.50  --dbg_dump_prop_clauses                 false
% 6.38/1.50  --dbg_dump_prop_clauses_file            -
% 6.38/1.50  --dbg_out_stat                          false
% 6.38/1.50  
% 6.38/1.50  
% 6.38/1.50  
% 6.38/1.50  
% 6.38/1.50  ------ Proving...
% 6.38/1.50  
% 6.38/1.50  
% 6.38/1.50  % SZS status Theorem for theBenchmark.p
% 6.38/1.50  
% 6.38/1.50   Resolution empty clause
% 6.38/1.50  
% 6.38/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 6.38/1.50  
% 6.38/1.50  fof(f10,conjecture,(
% 6.38/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f11,negated_conjecture,(
% 6.38/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.38/1.50    inference(negated_conjecture,[],[f10])).
% 6.38/1.50  
% 6.38/1.50  fof(f23,plain,(
% 6.38/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.38/1.50    inference(ennf_transformation,[],[f11])).
% 6.38/1.50  
% 6.38/1.50  fof(f24,plain,(
% 6.38/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.38/1.50    inference(flattening,[],[f23])).
% 6.38/1.50  
% 6.38/1.50  fof(f34,plain,(
% 6.38/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 6.38/1.50    introduced(choice_axiom,[])).
% 6.38/1.50  
% 6.38/1.50  fof(f33,plain,(
% 6.38/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 6.38/1.50    introduced(choice_axiom,[])).
% 6.38/1.50  
% 6.38/1.50  fof(f32,plain,(
% 6.38/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 6.38/1.50    introduced(choice_axiom,[])).
% 6.38/1.50  
% 6.38/1.50  fof(f31,plain,(
% 6.38/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 6.38/1.50    introduced(choice_axiom,[])).
% 6.38/1.50  
% 6.38/1.50  fof(f30,plain,(
% 6.38/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 6.38/1.50    introduced(choice_axiom,[])).
% 6.38/1.50  
% 6.38/1.50  fof(f29,plain,(
% 6.38/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 6.38/1.50    introduced(choice_axiom,[])).
% 6.38/1.50  
% 6.38/1.50  fof(f35,plain,(
% 6.38/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 6.38/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f24,f34,f33,f32,f31,f30,f29])).
% 6.38/1.50  
% 6.38/1.50  fof(f63,plain,(
% 6.38/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f3,axiom,(
% 6.38/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f13,plain,(
% 6.38/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 6.38/1.50    inference(ennf_transformation,[],[f3])).
% 6.38/1.50  
% 6.38/1.50  fof(f39,plain,(
% 6.38/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f13])).
% 6.38/1.50  
% 6.38/1.50  fof(f4,axiom,(
% 6.38/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f40,plain,(
% 6.38/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 6.38/1.50    inference(cnf_transformation,[],[f4])).
% 6.38/1.50  
% 6.38/1.50  fof(f5,axiom,(
% 6.38/1.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f14,plain,(
% 6.38/1.50    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 6.38/1.50    inference(ennf_transformation,[],[f5])).
% 6.38/1.50  
% 6.38/1.50  fof(f41,plain,(
% 6.38/1.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f14])).
% 6.38/1.50  
% 6.38/1.50  fof(f56,plain,(
% 6.38/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f2,axiom,(
% 6.38/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f12,plain,(
% 6.38/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.38/1.50    inference(ennf_transformation,[],[f2])).
% 6.38/1.50  
% 6.38/1.50  fof(f38,plain,(
% 6.38/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.38/1.50    inference(cnf_transformation,[],[f12])).
% 6.38/1.50  
% 6.38/1.50  fof(f64,plain,(
% 6.38/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f1,axiom,(
% 6.38/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f25,plain,(
% 6.38/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.38/1.50    inference(nnf_transformation,[],[f1])).
% 6.38/1.50  
% 6.38/1.50  fof(f36,plain,(
% 6.38/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f25])).
% 6.38/1.50  
% 6.38/1.50  fof(f6,axiom,(
% 6.38/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f15,plain,(
% 6.38/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.38/1.50    inference(ennf_transformation,[],[f6])).
% 6.38/1.50  
% 6.38/1.50  fof(f16,plain,(
% 6.38/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.38/1.50    inference(flattening,[],[f15])).
% 6.38/1.50  
% 6.38/1.50  fof(f26,plain,(
% 6.38/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.38/1.50    inference(nnf_transformation,[],[f16])).
% 6.38/1.50  
% 6.38/1.50  fof(f42,plain,(
% 6.38/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f26])).
% 6.38/1.50  
% 6.38/1.50  fof(f57,plain,(
% 6.38/1.50    r1_subset_1(sK2,sK3)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f53,plain,(
% 6.38/1.50    ~v1_xboole_0(sK2)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f55,plain,(
% 6.38/1.50    ~v1_xboole_0(sK3)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f7,axiom,(
% 6.38/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f17,plain,(
% 6.38/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.38/1.50    inference(ennf_transformation,[],[f7])).
% 6.38/1.50  
% 6.38/1.50  fof(f18,plain,(
% 6.38/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.38/1.50    inference(flattening,[],[f17])).
% 6.38/1.50  
% 6.38/1.50  fof(f44,plain,(
% 6.38/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f18])).
% 6.38/1.50  
% 6.38/1.50  fof(f61,plain,(
% 6.38/1.50    v1_funct_1(sK5)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f60,plain,(
% 6.38/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f58,plain,(
% 6.38/1.50    v1_funct_1(sK4)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f9,axiom,(
% 6.38/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f21,plain,(
% 6.38/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.38/1.50    inference(ennf_transformation,[],[f9])).
% 6.38/1.50  
% 6.38/1.50  fof(f22,plain,(
% 6.38/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.38/1.50    inference(flattening,[],[f21])).
% 6.38/1.50  
% 6.38/1.50  fof(f50,plain,(
% 6.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f22])).
% 6.38/1.50  
% 6.38/1.50  fof(f48,plain,(
% 6.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f22])).
% 6.38/1.50  
% 6.38/1.50  fof(f52,plain,(
% 6.38/1.50    ~v1_xboole_0(sK1)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f62,plain,(
% 6.38/1.50    v1_funct_2(sK5,sK3,sK1)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f59,plain,(
% 6.38/1.50    v1_funct_2(sK4,sK2,sK1)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f51,plain,(
% 6.38/1.50    ~v1_xboole_0(sK0)),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f54,plain,(
% 6.38/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.38/1.50    inference(cnf_transformation,[],[f35])).
% 6.38/1.50  
% 6.38/1.50  fof(f8,axiom,(
% 6.38/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 6.38/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.38/1.50  
% 6.38/1.50  fof(f19,plain,(
% 6.38/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.38/1.50    inference(ennf_transformation,[],[f8])).
% 6.38/1.50  
% 6.38/1.50  fof(f20,plain,(
% 6.38/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.38/1.50    inference(flattening,[],[f19])).
% 6.38/1.50  
% 6.38/1.50  fof(f27,plain,(
% 6.38/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.38/1.50    inference(nnf_transformation,[],[f20])).
% 6.38/1.50  
% 6.38/1.50  fof(f28,plain,(
% 6.38/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.38/1.50    inference(flattening,[],[f27])).
% 6.38/1.50  
% 6.38/1.50  fof(f45,plain,(
% 6.38/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f28])).
% 6.38/1.50  
% 6.38/1.50  fof(f68,plain,(
% 6.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(equality_resolution,[],[f45])).
% 6.38/1.50  
% 6.38/1.50  fof(f49,plain,(
% 6.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f22])).
% 6.38/1.50  
% 6.38/1.50  fof(f46,plain,(
% 6.38/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(cnf_transformation,[],[f28])).
% 6.38/1.50  
% 6.38/1.50  fof(f67,plain,(
% 6.38/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.38/1.50    inference(equality_resolution,[],[f46])).
% 6.38/1.50  
% 6.38/1.50  cnf(c_16,negated_conjecture,
% 6.38/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.38/1.50      inference(cnf_transformation,[],[f63]) ).
% 6.38/1.50  
% 6.38/1.50  cnf(c_568,negated_conjecture,
% 6.38/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.38/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 6.38/1.50  
% 6.38/1.50  cnf(c_1022,plain,
% 6.38/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.38/1.50      inference(predicate_to_equality,[status(thm)],[c_568]) ).
% 6.38/1.50  
% 6.38/1.50  cnf(c_3,plain,
% 6.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 6.38/1.50      inference(cnf_transformation,[],[f39]) ).
% 6.38/1.50  
% 6.38/1.50  cnf(c_577,plain,
% 6.38/1.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 6.38/1.50      | ~ v1_relat_1(X1_50)
% 6.38/1.50      | v1_relat_1(X0_50) ),
% 6.38/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1014,plain,
% 6.38/1.51      ( m1_subset_1(X0_50,k1_zfmisc_1(X1_50)) != iProver_top
% 6.38/1.51      | v1_relat_1(X1_50) != iProver_top
% 6.38/1.51      | v1_relat_1(X0_50) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2128,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 6.38/1.51      | v1_relat_1(sK5) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1022,c_1014]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_41,plain,
% 6.38/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1319,plain,
% 6.38/1.51      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 6.38/1.51      | v1_relat_1(X0_50)
% 6.38/1.51      | ~ v1_relat_1(k2_zfmisc_1(X1_50,X2_50)) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_577]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1522,plain,
% 6.38/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 6.38/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 6.38/1.51      | v1_relat_1(sK5) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_1319]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1523,plain,
% 6.38/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.38/1.51      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 6.38/1.51      | v1_relat_1(sK5) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_1522]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_4,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 6.38/1.51      inference(cnf_transformation,[],[f40]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_576,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(X0_50,X1_50)) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2219,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_576]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2220,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_2219]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2440,plain,
% 6.38/1.51      ( v1_relat_1(sK5) = iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_2128,c_41,c_1523,c_2220]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_5,plain,
% 6.38/1.51      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.38/1.51      inference(cnf_transformation,[],[f41]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_575,plain,
% 6.38/1.51      ( ~ v1_relat_1(X0_50) | k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0 ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_5]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1016,plain,
% 6.38/1.51      ( k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0
% 6.38/1.51      | v1_relat_1(X0_50) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_575]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2445,plain,
% 6.38/1.51      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2440,c_1016]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_23,negated_conjecture,
% 6.38/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.38/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_562,negated_conjecture,
% 6.38/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_23]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1028,plain,
% 6.38/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2,plain,
% 6.38/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.38/1.51      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 6.38/1.51      inference(cnf_transformation,[],[f38]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_578,plain,
% 6.38/1.51      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 6.38/1.51      | k9_subset_1(X1_50,X2_50,X0_50) = k3_xboole_0(X2_50,X0_50) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1013,plain,
% 6.38/1.51      ( k9_subset_1(X0_50,X1_50,X2_50) = k3_xboole_0(X1_50,X2_50)
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1802,plain,
% 6.38/1.51      ( k9_subset_1(sK0,X0_50,sK3) = k3_xboole_0(X0_50,sK3) ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1028,c_1013]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_15,negated_conjecture,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.38/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_569,negated_conjecture,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_15]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2074,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_1802,c_569]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1,plain,
% 6.38/1.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.38/1.51      inference(cnf_transformation,[],[f36]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_211,plain,
% 6.38/1.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.38/1.51      inference(prop_impl,[status(thm)],[c_1]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_7,plain,
% 6.38/1.51      ( ~ r1_subset_1(X0,X1)
% 6.38/1.51      | r1_xboole_0(X0,X1)
% 6.38/1.51      | v1_xboole_0(X0)
% 6.38/1.51      | v1_xboole_0(X1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f42]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_22,negated_conjecture,
% 6.38/1.51      ( r1_subset_1(sK2,sK3) ),
% 6.38/1.51      inference(cnf_transformation,[],[f57]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_378,plain,
% 6.38/1.51      ( r1_xboole_0(X0,X1)
% 6.38/1.51      | v1_xboole_0(X0)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | sK3 != X1
% 6.38/1.51      | sK2 != X0 ),
% 6.38/1.51      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_379,plain,
% 6.38/1.51      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 6.38/1.51      inference(unflattening,[status(thm)],[c_378]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_26,negated_conjecture,
% 6.38/1.51      ( ~ v1_xboole_0(sK2) ),
% 6.38/1.51      inference(cnf_transformation,[],[f53]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_24,negated_conjecture,
% 6.38/1.51      ( ~ v1_xboole_0(sK3) ),
% 6.38/1.51      inference(cnf_transformation,[],[f55]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_381,plain,
% 6.38/1.51      ( r1_xboole_0(sK2,sK3) ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_379,c_26,c_24]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_392,plain,
% 6.38/1.51      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 6.38/1.51      inference(resolution_lifted,[status(thm)],[c_211,c_381]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_393,plain,
% 6.38/1.51      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.38/1.51      inference(unflattening,[status(thm)],[c_392]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_554,plain,
% 6.38/1.51      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_393]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2075,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_2074,c_554]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_8,plain,
% 6.38/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.38/1.51      inference(cnf_transformation,[],[f44]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_574,plain,
% 6.38/1.51      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 6.38/1.51      | ~ v1_funct_1(X0_50)
% 6.38/1.51      | k2_partfun1(X1_50,X2_50,X0_50,X3_50) = k7_relat_1(X0_50,X3_50) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1017,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,X1_50,X2_50,X3_50) = k7_relat_1(X2_50,X3_50)
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 6.38/1.51      | v1_funct_1(X2_50) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2189,plain,
% 6.38/1.51      ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50)
% 6.38/1.51      | v1_funct_1(sK5) != iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1022,c_1017]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_18,negated_conjecture,
% 6.38/1.51      ( v1_funct_1(sK5) ),
% 6.38/1.51      inference(cnf_transformation,[],[f61]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1385,plain,
% 6.38/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 6.38/1.51      | ~ v1_funct_1(sK5)
% 6.38/1.51      | k2_partfun1(X0_50,X1_50,sK5,X2_50) = k7_relat_1(sK5,X2_50) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_574]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1528,plain,
% 6.38/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 6.38/1.51      | ~ v1_funct_1(sK5)
% 6.38/1.51      | k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_1385]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2529,plain,
% 6.38/1.51      ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_2189,c_18,c_16,c_1528]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_19,negated_conjecture,
% 6.38/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.38/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_565,negated_conjecture,
% 6.38/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_19]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1025,plain,
% 6.38/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2190,plain,
% 6.38/1.51      ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50)
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1025,c_1017]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_21,negated_conjecture,
% 6.38/1.51      ( v1_funct_1(sK4) ),
% 6.38/1.51      inference(cnf_transformation,[],[f58]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1390,plain,
% 6.38/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 6.38/1.51      | ~ v1_funct_1(sK4)
% 6.38/1.51      | k2_partfun1(X0_50,X1_50,sK4,X2_50) = k7_relat_1(sK4,X2_50) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_574]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1533,plain,
% 6.38/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.38/1.51      | ~ v1_funct_1(sK4)
% 6.38/1.51      | k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_1390]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2597,plain,
% 6.38/1.51      ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_2190,c_21,c_19,c_1533]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2601,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_2075,c_2529,c_2597]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2961,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_2445,c_2601]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1525,plain,
% 6.38/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.38/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 6.38/1.51      | v1_relat_1(sK4) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_1319]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1784,plain,
% 6.38/1.51      ( ~ v1_relat_1(sK4) | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_575]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2223,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 6.38/1.51      inference(instantiation,[status(thm)],[c_576]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_14889,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_2961,c_19,c_1525,c_1784,c_2223]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_14890,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_14889]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_12,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f50]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_572,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 6.38/1.51      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 6.38/1.51      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 6.38/1.51      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 6.38/1.51      | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50)))
% 6.38/1.51      | ~ v1_funct_1(X0_50)
% 6.38/1.51      | ~ v1_funct_1(X3_50)
% 6.38/1.51      | v1_xboole_0(X1_50)
% 6.38/1.51      | v1_xboole_0(X2_50)
% 6.38/1.51      | v1_xboole_0(X4_50)
% 6.38/1.51      | v1_xboole_0(X5_50) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_12]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1019,plain,
% 6.38/1.51      ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
% 6.38/1.51      | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
% 6.38/1.51      | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50))) = iProver_top
% 6.38/1.51      | v1_funct_1(X0_50) != iProver_top
% 6.38/1.51      | v1_funct_1(X3_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X5_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X4_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2264,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
% 6.38/1.51      | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
% 6.38/1.51      | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
% 6.38/1.51      | v1_funct_1(X5_50) != iProver_top
% 6.38/1.51      | v1_funct_1(X4_50) != iProver_top
% 6.38/1.51      | v1_funct_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50)) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X3_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1019,c_1017]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_14,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f48]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_570,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 6.38/1.51      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 6.38/1.51      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 6.38/1.51      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 6.38/1.51      | ~ v1_funct_1(X0_50)
% 6.38/1.51      | ~ v1_funct_1(X3_50)
% 6.38/1.51      | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50))
% 6.38/1.51      | v1_xboole_0(X1_50)
% 6.38/1.51      | v1_xboole_0(X2_50)
% 6.38/1.51      | v1_xboole_0(X4_50)
% 6.38/1.51      | v1_xboole_0(X5_50) ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_14]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1021,plain,
% 6.38/1.51      ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
% 6.38/1.51      | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
% 6.38/1.51      | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
% 6.38/1.51      | v1_funct_1(X0_50) != iProver_top
% 6.38/1.51      | v1_funct_1(X3_50) != iProver_top
% 6.38/1.51      | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50)) = iProver_top
% 6.38/1.51      | v1_xboole_0(X5_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X4_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_6514,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
% 6.38/1.51      | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
% 6.38/1.51      | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
% 6.38/1.51      | v1_funct_1(X5_50) != iProver_top
% 6.38/1.51      | v1_funct_1(X4_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X3_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(forward_subsumption_resolution,[status(thm)],[c_2264,c_1021]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_6518,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
% 6.38/1.51      | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
% 6.38/1.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(X2_50) != iProver_top
% 6.38/1.51      | v1_funct_1(sK5) != iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK1) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1022,c_6514]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_27,negated_conjecture,
% 6.38/1.51      ( ~ v1_xboole_0(sK1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f52]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_30,plain,
% 6.38/1.51      ( v1_xboole_0(sK1) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_33,plain,
% 6.38/1.51      ( v1_xboole_0(sK3) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_39,plain,
% 6.38/1.51      ( v1_funct_1(sK5) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_17,negated_conjecture,
% 6.38/1.51      ( v1_funct_2(sK5,sK3,sK1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f62]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_40,plain,
% 6.38/1.51      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_6625,plain,
% 6.38/1.51      ( v1_funct_1(X2_50) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
% 6.38/1.51      | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_6518,c_30,c_33,c_39,c_40]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_6626,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
% 6.38/1.51      | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(X2_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_6625]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_6640,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1025,c_6626]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_31,plain,
% 6.38/1.51      ( v1_xboole_0(sK2) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_36,plain,
% 6.38/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_20,negated_conjecture,
% 6.38/1.51      ( v1_funct_2(sK4,sK2,sK1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f59]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_37,plain,
% 6.38/1.51      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_7233,plain,
% 6.38/1.51      ( v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_6640,c_31,c_36,c_37]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_7234,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_7233]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_7243,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50)
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1028,c_7234]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_28,negated_conjecture,
% 6.38/1.51      ( ~ v1_xboole_0(sK0) ),
% 6.38/1.51      inference(cnf_transformation,[],[f51]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_29,plain,
% 6.38/1.51      ( v1_xboole_0(sK0) != iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_25,negated_conjecture,
% 6.38/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 6.38/1.51      inference(cnf_transformation,[],[f54]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_32,plain,
% 6.38/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_7248,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_7243,c_29,c_32]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_11,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.38/1.51      inference(cnf_transformation,[],[f68]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1) ),
% 6.38/1.51      inference(cnf_transformation,[],[f49]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_156,plain,
% 6.38/1.51      ( ~ v1_funct_1(X3)
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_11,c_14,c_13,c_12]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_157,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_156]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_556,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 6.38/1.51      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 6.38/1.51      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 6.38/1.51      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 6.38/1.51      | ~ v1_funct_1(X0_50)
% 6.38/1.51      | ~ v1_funct_1(X3_50)
% 6.38/1.51      | v1_xboole_0(X1_50)
% 6.38/1.51      | v1_xboole_0(X2_50)
% 6.38/1.51      | v1_xboole_0(X4_50)
% 6.38/1.51      | v1_xboole_0(X5_50)
% 6.38/1.51      | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X4_50) = X3_50 ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_157]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1034,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X4_50) = X5_50
% 6.38/1.51      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 6.38/1.51      | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
% 6.38/1.51      | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
% 6.38/1.51      | v1_funct_1(X2_50) != iProver_top
% 6.38/1.51      | v1_funct_1(X5_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X3_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X4_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_4142,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_funct_1(sK5) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK1) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2529,c_1034]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10050,plain,
% 6.38/1.51      ( v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_4142,c_30,c_33,c_39,c_40,c_41]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10051,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_10050]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10071,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1802,c_10051]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10081,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_10071,c_1802]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_34,plain,
% 6.38/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10342,plain,
% 6.38/1.51      ( v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_10081,c_29,c_34]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10343,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_10342]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10356,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2597,c_10343]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2129,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 6.38/1.51      | v1_relat_1(sK4) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1025,c_1014]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_38,plain,
% 6.38/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1526,plain,
% 6.38/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 6.38/1.51      | v1_relat_1(sK4) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2224,plain,
% 6.38/1.51      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_2223]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2522,plain,
% 6.38/1.51      ( v1_relat_1(sK4) = iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_2129,c_38,c_1526,c_2224]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_2527,plain,
% 6.38/1.51      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2522,c_1016]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10440,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k1_xboole_0 != k1_xboole_0
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_10356,c_554,c_2445,c_2527]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10441,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(equality_resolution_simp,[status(thm)],[c_10440]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10442,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_10441,c_7248]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10066,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2597,c_10051]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10276,plain,
% 6.38/1.51      ( v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_10066,c_31,c_36,c_37,c_38]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10277,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_10276]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10287,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1802,c_10277]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10288,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_10287,c_554,c_2445]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10289,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_10288,c_1802,c_7248]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10290,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | k1_xboole_0 != k1_xboole_0
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_10289,c_554,c_2527]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10291,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(equality_resolution_simp,[status(thm)],[c_10290]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10465,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_10442,c_29,c_32,c_34,c_10291]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_10,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.38/1.51      inference(cnf_transformation,[],[f67]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_163,plain,
% 6.38/1.51      ( ~ v1_funct_1(X3)
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_10,c_14,c_13,c_12]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_164,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 6.38/1.51      | ~ v1_funct_2(X3,X4,X2)
% 6.38/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.38/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.38/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.38/1.51      | ~ v1_funct_1(X0)
% 6.38/1.51      | ~ v1_funct_1(X3)
% 6.38/1.51      | v1_xboole_0(X1)
% 6.38/1.51      | v1_xboole_0(X2)
% 6.38/1.51      | v1_xboole_0(X4)
% 6.38/1.51      | v1_xboole_0(X5)
% 6.38/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_163]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_555,plain,
% 6.38/1.51      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 6.38/1.51      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 6.38/1.51      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 6.38/1.51      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 6.38/1.51      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 6.38/1.51      | ~ v1_funct_1(X0_50)
% 6.38/1.51      | ~ v1_funct_1(X3_50)
% 6.38/1.51      | v1_xboole_0(X1_50)
% 6.38/1.51      | v1_xboole_0(X2_50)
% 6.38/1.51      | v1_xboole_0(X4_50)
% 6.38/1.51      | v1_xboole_0(X5_50)
% 6.38/1.51      | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X1_50) = X0_50 ),
% 6.38/1.51      inference(subtyping,[status(esa)],[c_164]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_1035,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X0_50) = X2_50
% 6.38/1.51      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 6.38/1.51      | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
% 6.38/1.51      | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 6.38/1.51      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
% 6.38/1.51      | v1_funct_1(X2_50) != iProver_top
% 6.38/1.51      | v1_funct_1(X5_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X3_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X1_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X4_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_5712,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_funct_1(sK5) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK1) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2529,c_1035]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13496,plain,
% 6.38/1.51      ( v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_5712,c_30,c_33,c_39,c_40,c_41]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13497,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X2_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_13496]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13517,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1802,c_13497]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13527,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_13517,c_1802]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13694,plain,
% 6.38/1.51      ( v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_13527,c_29,c_34]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13695,plain,
% 6.38/1.51      ( k2_partfun1(X0_50,sK1,X1_50,k3_xboole_0(X0_50,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_50,sK3))
% 6.38/1.51      | k2_partfun1(k4_subset_1(sK0,X0_50,sK3),sK1,k1_tmap_1(sK0,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(X0_50,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(X1_50) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_13694]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13708,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2597,c_13695]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13792,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k1_xboole_0 != k1_xboole_0
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_13708,c_554,c_2445,c_2527]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13793,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(equality_resolution_simp,[status(thm)],[c_13792]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13794,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_13793,c_7248]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13512,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 6.38/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.38/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_funct_1(sK4) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_2597,c_13497]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13676,plain,
% 6.38/1.51      ( v1_xboole_0(X0_50) = iProver_top
% 6.38/1.51      | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_13512,c_31,c_36,c_37,c_38]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13677,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 6.38/1.51      | v1_xboole_0(X0_50) = iProver_top ),
% 6.38/1.51      inference(renaming,[status(thm)],[c_13676]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13687,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(superposition,[status(thm)],[c_1802,c_13677]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13688,plain,
% 6.38/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_13687,c_554,c_2445]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13689,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_13688,c_1802,c_7248]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13690,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | k1_xboole_0 != k1_xboole_0
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(light_normalisation,[status(thm)],[c_13689,c_554,c_2527]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13691,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.38/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.38/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 6.38/1.51      inference(equality_resolution_simp,[status(thm)],[c_13690]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_13860,plain,
% 6.38/1.51      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 6.38/1.51      inference(global_propositional_subsumption,
% 6.38/1.51                [status(thm)],
% 6.38/1.51                [c_13794,c_29,c_32,c_34,c_13691]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_14891,plain,
% 6.38/1.51      ( sK5 != sK5 | sK4 != sK4 ),
% 6.38/1.51      inference(demodulation,[status(thm)],[c_14890,c_7248,c_10465,c_13860]) ).
% 6.38/1.51  
% 6.38/1.51  cnf(c_14892,plain,
% 6.38/1.51      ( $false ),
% 6.38/1.51      inference(equality_resolution_simp,[status(thm)],[c_14891]) ).
% 6.38/1.51  
% 6.38/1.51  
% 6.38/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.38/1.51  
% 6.38/1.51  ------                               Statistics
% 6.38/1.51  
% 6.38/1.51  ------ General
% 6.38/1.51  
% 6.38/1.51  abstr_ref_over_cycles:                  0
% 6.38/1.51  abstr_ref_under_cycles:                 0
% 6.38/1.51  gc_basic_clause_elim:                   0
% 6.38/1.51  forced_gc_time:                         0
% 6.38/1.51  parsing_time:                           0.018
% 6.38/1.51  unif_index_cands_time:                  0.
% 6.38/1.51  unif_index_add_time:                    0.
% 6.38/1.51  orderings_time:                         0.
% 6.38/1.51  out_proof_time:                         0.021
% 6.38/1.51  total_time:                             0.776
% 6.38/1.51  num_of_symbols:                         55
% 6.38/1.51  num_of_terms:                           31630
% 6.38/1.51  
% 6.38/1.51  ------ Preprocessing
% 6.38/1.51  
% 6.38/1.51  num_of_splits:                          0
% 6.38/1.51  num_of_split_atoms:                     0
% 6.38/1.51  num_of_reused_defs:                     0
% 6.38/1.51  num_eq_ax_congr_red:                    7
% 6.38/1.51  num_of_sem_filtered_clauses:            1
% 6.38/1.51  num_of_subtypes:                        2
% 6.38/1.51  monotx_restored_types:                  0
% 6.38/1.51  sat_num_of_epr_types:                   0
% 6.38/1.51  sat_num_of_non_cyclic_types:            0
% 6.38/1.51  sat_guarded_non_collapsed_types:        1
% 6.38/1.51  num_pure_diseq_elim:                    0
% 6.38/1.51  simp_replaced_by:                       0
% 6.38/1.51  res_preprocessed:                       137
% 6.38/1.51  prep_upred:                             0
% 6.38/1.51  prep_unflattend:                        4
% 6.38/1.51  smt_new_axioms:                         0
% 6.38/1.51  pred_elim_cands:                        5
% 6.38/1.51  pred_elim:                              2
% 6.38/1.51  pred_elim_cl:                           4
% 6.38/1.51  pred_elim_cycles:                       4
% 6.38/1.51  merged_defs:                            2
% 6.38/1.51  merged_defs_ncl:                        0
% 6.38/1.51  bin_hyper_res:                          2
% 6.38/1.51  prep_cycles:                            4
% 6.38/1.51  pred_elim_time:                         0.001
% 6.38/1.51  splitting_time:                         0.
% 6.38/1.51  sem_filter_time:                        0.
% 6.38/1.51  monotx_time:                            0.
% 6.38/1.51  subtype_inf_time:                       0.001
% 6.38/1.51  
% 6.38/1.51  ------ Problem properties
% 6.38/1.51  
% 6.38/1.51  clauses:                                25
% 6.38/1.51  conjectures:                            13
% 6.38/1.51  epr:                                    8
% 6.38/1.51  horn:                                   19
% 6.38/1.51  ground:                                 14
% 6.38/1.51  unary:                                  14
% 6.38/1.51  binary:                                 2
% 6.38/1.51  lits:                                   111
% 6.38/1.51  lits_eq:                                13
% 6.38/1.51  fd_pure:                                0
% 6.38/1.51  fd_pseudo:                              0
% 6.38/1.51  fd_cond:                                0
% 6.38/1.51  fd_pseudo_cond:                         0
% 6.38/1.51  ac_symbols:                             0
% 6.38/1.51  
% 6.38/1.51  ------ Propositional Solver
% 6.38/1.51  
% 6.38/1.51  prop_solver_calls:                      27
% 6.38/1.51  prop_fast_solver_calls:                 3141
% 6.38/1.51  smt_solver_calls:                       0
% 6.38/1.51  smt_fast_solver_calls:                  0
% 6.38/1.51  prop_num_of_clauses:                    5782
% 6.38/1.51  prop_preprocess_simplified:             9354
% 6.38/1.51  prop_fo_subsumed:                       241
% 6.38/1.51  prop_solver_time:                       0.
% 6.38/1.51  smt_solver_time:                        0.
% 6.38/1.51  smt_fast_solver_time:                   0.
% 6.38/1.51  prop_fast_solver_time:                  0.
% 6.38/1.51  prop_unsat_core_time:                   0.
% 6.38/1.51  
% 6.38/1.51  ------ QBF
% 6.38/1.51  
% 6.38/1.51  qbf_q_res:                              0
% 6.38/1.51  qbf_num_tautologies:                    0
% 6.38/1.51  qbf_prep_cycles:                        0
% 6.38/1.51  
% 6.38/1.51  ------ BMC1
% 6.38/1.51  
% 6.38/1.51  bmc1_current_bound:                     -1
% 6.38/1.51  bmc1_last_solved_bound:                 -1
% 6.38/1.51  bmc1_unsat_core_size:                   -1
% 6.38/1.51  bmc1_unsat_core_parents_size:           -1
% 6.38/1.51  bmc1_merge_next_fun:                    0
% 6.38/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.38/1.51  
% 6.38/1.51  ------ Instantiation
% 6.38/1.51  
% 6.38/1.51  inst_num_of_clauses:                    1261
% 6.38/1.51  inst_num_in_passive:                    61
% 6.38/1.51  inst_num_in_active:                     678
% 6.38/1.51  inst_num_in_unprocessed:                522
% 6.38/1.51  inst_num_of_loops:                      700
% 6.38/1.51  inst_num_of_learning_restarts:          0
% 6.38/1.51  inst_num_moves_active_passive:          18
% 6.38/1.51  inst_lit_activity:                      0
% 6.38/1.51  inst_lit_activity_moves:                0
% 6.38/1.51  inst_num_tautologies:                   0
% 6.38/1.51  inst_num_prop_implied:                  0
% 6.38/1.51  inst_num_existing_simplified:           0
% 6.38/1.51  inst_num_eq_res_simplified:             0
% 6.38/1.51  inst_num_child_elim:                    0
% 6.38/1.51  inst_num_of_dismatching_blockings:      174
% 6.38/1.51  inst_num_of_non_proper_insts:           901
% 6.38/1.51  inst_num_of_duplicates:                 0
% 6.38/1.51  inst_inst_num_from_inst_to_res:         0
% 6.38/1.51  inst_dismatching_checking_time:         0.
% 6.38/1.51  
% 6.38/1.51  ------ Resolution
% 6.38/1.51  
% 6.38/1.51  res_num_of_clauses:                     0
% 6.38/1.51  res_num_in_passive:                     0
% 6.38/1.51  res_num_in_active:                      0
% 6.38/1.51  res_num_of_loops:                       141
% 6.38/1.51  res_forward_subset_subsumed:            42
% 6.38/1.51  res_backward_subset_subsumed:           0
% 6.38/1.51  res_forward_subsumed:                   0
% 6.38/1.51  res_backward_subsumed:                  0
% 6.38/1.51  res_forward_subsumption_resolution:     0
% 6.38/1.51  res_backward_subsumption_resolution:    0
% 6.38/1.51  res_clause_to_clause_subsumption:       2264
% 6.38/1.51  res_orphan_elimination:                 0
% 6.38/1.51  res_tautology_del:                      30
% 6.38/1.51  res_num_eq_res_simplified:              0
% 6.38/1.51  res_num_sel_changes:                    0
% 6.38/1.51  res_moves_from_active_to_pass:          0
% 6.38/1.51  
% 6.38/1.51  ------ Superposition
% 6.38/1.51  
% 6.38/1.51  sup_time_total:                         0.
% 6.38/1.51  sup_time_generating:                    0.
% 6.38/1.51  sup_time_sim_full:                      0.
% 6.38/1.51  sup_time_sim_immed:                     0.
% 6.38/1.51  
% 6.38/1.51  sup_num_of_clauses:                     248
% 6.38/1.51  sup_num_in_active:                      136
% 6.38/1.51  sup_num_in_passive:                     112
% 6.38/1.51  sup_num_of_loops:                       138
% 6.38/1.51  sup_fw_superposition:                   231
% 6.38/1.51  sup_bw_superposition:                   42
% 6.38/1.51  sup_immediate_simplified:               126
% 6.38/1.51  sup_given_eliminated:                   0
% 6.38/1.51  comparisons_done:                       0
% 6.38/1.51  comparisons_avoided:                    0
% 6.38/1.51  
% 6.38/1.51  ------ Simplifications
% 6.38/1.51  
% 6.38/1.51  
% 6.38/1.51  sim_fw_subset_subsumed:                 0
% 6.38/1.51  sim_bw_subset_subsumed:                 2
% 6.38/1.51  sim_fw_subsumed:                        15
% 6.38/1.51  sim_bw_subsumed:                        8
% 6.38/1.51  sim_fw_subsumption_res:                 6
% 6.38/1.51  sim_bw_subsumption_res:                 0
% 6.38/1.51  sim_tautology_del:                      0
% 6.38/1.51  sim_eq_tautology_del:                   7
% 6.38/1.51  sim_eq_res_simp:                        7
% 6.38/1.51  sim_fw_demodulated:                     76
% 6.38/1.51  sim_bw_demodulated:                     2
% 6.38/1.51  sim_light_normalised:                   49
% 6.38/1.51  sim_joinable_taut:                      0
% 6.38/1.51  sim_joinable_simp:                      0
% 6.38/1.51  sim_ac_normalised:                      0
% 6.38/1.51  sim_smt_subsumption:                    0
% 6.38/1.51  
%------------------------------------------------------------------------------
