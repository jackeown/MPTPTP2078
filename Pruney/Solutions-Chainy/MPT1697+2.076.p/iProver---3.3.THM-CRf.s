%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:39 EST 2020

% Result     : Theorem 7.37s
% Output     : CNFRefutation 7.37s
% Verified   : 
% Statistics : Number of formulae       :  219 (2364 expanded)
%              Number of clauses        :  149 ( 669 expanded)
%              Number of leaves         :   19 ( 898 expanded)
%              Depth                    :   23
%              Number of atoms          : 1228 (29661 expanded)
%              Number of equality atoms :  507 (7117 expanded)
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

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f49,f48,f47,f46,f45,f44])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f69,plain,(
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

fof(f91,plain,(
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
    inference(equality_resolution,[],[f69])).

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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f75,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f68,plain,(
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

fof(f92,plain,(
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
    inference(equality_resolution,[],[f68])).

fof(f87,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_838,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1636,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_855,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1620,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_2294,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1636,c_1620])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_844,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1630,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1625,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_3052,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_1625])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2058,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_2236,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_3283,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3052,c_26,c_24,c_2236])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_841,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1633,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_3053,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1625])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2063,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_2241,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_3646,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_29,c_27,c_2241])).

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
    inference(cnf_transformation,[],[f91])).

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
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_205,plain,
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

cnf(c_206,plain,
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
    inference(renaming,[status(thm)],[c_205])).

cnf(c_831,plain,
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
    inference(subtyping,[status(esa)],[c_206])).

cnf(c_1643,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_854,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1621,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_1854,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1643,c_1621])).

cnf(c_7341,plain,
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
    inference(superposition,[status(thm)],[c_3646,c_1854])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17426,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7341,c_38,c_39,c_44,c_45,c_46])).

cnf(c_17427,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_17426])).

cnf(c_17440,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3283,c_17427])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17781,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17440,c_41,c_47,c_48,c_49])).

cnf(c_17791,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2294,c_17781])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_508,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_509,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_511,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_34,c_32])).

cnf(c_830,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_511])).

cnf(c_1644,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_858,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1617,plain,
    ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2665,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1644,c_1617])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1622,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_2717,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_1622])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_2414,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_2415,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2414])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_852,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2531,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_2532,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2531])).

cnf(c_2924,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2717,c_49,c_2415,c_2532])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_856,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1619,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_857,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1618,plain,
    ( r1_xboole_0(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X1_53,X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_2704,plain,
    ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1619,c_1618])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_851,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1624,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_3271,plain,
    ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2704,c_1624])).

cnf(c_3811,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2924,c_3271])).

cnf(c_17792,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17791,c_2665,c_3811])).

cnf(c_848,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1627,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_xboole_0(X5_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_1799,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1627,c_1621])).

cnf(c_4906,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_1625])).

cnf(c_846,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1629,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
    | v1_xboole_0(X5_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_1747,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1629,c_1621])).

cnf(c_7971,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4906,c_1747])).

cnf(c_7975,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1630,c_7971])).

cnf(c_8074,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7975,c_38,c_41,c_47,c_48])).

cnf(c_8075,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_8074])).

cnf(c_8088,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_8075])).

cnf(c_8479,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8088,c_39,c_44,c_45])).

cnf(c_8488,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_8479])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8493,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8488,c_40])).

cnf(c_17793,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17792,c_2294,c_8493])).

cnf(c_2718,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1633,c_1622])).

cnf(c_2417,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_2418,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_2534,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_2535,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2534])).

cnf(c_2991,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2718,c_46,c_2418,c_2535])).

cnf(c_3812,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2991,c_3271])).

cnf(c_17794,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17793,c_2665,c_3812])).

cnf(c_17795,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17794])).

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
    inference(cnf_transformation,[],[f92])).

cnf(c_198,plain,
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

cnf(c_199,plain,
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
    inference(renaming,[status(thm)],[c_198])).

cnf(c_832,plain,
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
    inference(subtyping,[status(esa)],[c_199])).

cnf(c_1642,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_1826,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1642,c_1621])).

cnf(c_5257,plain,
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
    inference(superposition,[status(thm)],[c_3646,c_1826])).

cnf(c_14963,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5257,c_38,c_39,c_44,c_45,c_46])).

cnf(c_14964,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_14963])).

cnf(c_14977,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3283,c_14964])).

cnf(c_15335,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14977,c_41,c_47,c_48,c_49])).

cnf(c_15345,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2294,c_15335])).

cnf(c_15346,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15345,c_2665,c_3811])).

cnf(c_15347,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15346,c_2294,c_8493])).

cnf(c_15348,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15347,c_2665,c_3812])).

cnf(c_15349,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15348])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_845,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2474,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2294,c_845])).

cnf(c_2997,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2665,c_2474])).

cnf(c_3650,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2997,c_3283,c_3646])).

cnf(c_3821,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3811,c_3650])).

cnf(c_4587,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3821,c_3812])).

cnf(c_4588,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_4587])).

cnf(c_8497,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_8493,c_4588])).

cnf(c_8498,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_8497,c_8493])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17795,c_15349,c_8498,c_42,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:19:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.37/1.47  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.37/1.47  
% 7.37/1.47  ------  iProver source info
% 7.37/1.47  
% 7.37/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.37/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.37/1.47  git: non_committed_changes: false
% 7.37/1.47  git: last_make_outside_of_git: false
% 7.37/1.47  
% 7.37/1.47  ------ 
% 7.37/1.47  
% 7.37/1.47  ------ Input Options
% 7.37/1.47  
% 7.37/1.47  --out_options                           all
% 7.37/1.47  --tptp_safe_out                         true
% 7.37/1.47  --problem_path                          ""
% 7.37/1.47  --include_path                          ""
% 7.37/1.47  --clausifier                            res/vclausify_rel
% 7.37/1.47  --clausifier_options                    --mode clausify
% 7.37/1.47  --stdin                                 false
% 7.37/1.47  --stats_out                             all
% 7.37/1.47  
% 7.37/1.47  ------ General Options
% 7.37/1.47  
% 7.37/1.47  --fof                                   false
% 7.37/1.47  --time_out_real                         305.
% 7.37/1.47  --time_out_virtual                      -1.
% 7.37/1.47  --symbol_type_check                     false
% 7.37/1.47  --clausify_out                          false
% 7.37/1.47  --sig_cnt_out                           false
% 7.37/1.47  --trig_cnt_out                          false
% 7.37/1.47  --trig_cnt_out_tolerance                1.
% 7.37/1.47  --trig_cnt_out_sk_spl                   false
% 7.37/1.47  --abstr_cl_out                          false
% 7.37/1.47  
% 7.37/1.47  ------ Global Options
% 7.37/1.47  
% 7.37/1.47  --schedule                              default
% 7.37/1.47  --add_important_lit                     false
% 7.37/1.47  --prop_solver_per_cl                    1000
% 7.37/1.47  --min_unsat_core                        false
% 7.37/1.47  --soft_assumptions                      false
% 7.37/1.47  --soft_lemma_size                       3
% 7.37/1.47  --prop_impl_unit_size                   0
% 7.37/1.47  --prop_impl_unit                        []
% 7.37/1.47  --share_sel_clauses                     true
% 7.37/1.47  --reset_solvers                         false
% 7.37/1.47  --bc_imp_inh                            [conj_cone]
% 7.37/1.47  --conj_cone_tolerance                   3.
% 7.37/1.47  --extra_neg_conj                        none
% 7.37/1.47  --large_theory_mode                     true
% 7.37/1.47  --prolific_symb_bound                   200
% 7.37/1.47  --lt_threshold                          2000
% 7.37/1.47  --clause_weak_htbl                      true
% 7.37/1.47  --gc_record_bc_elim                     false
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing Options
% 7.37/1.47  
% 7.37/1.47  --preprocessing_flag                    true
% 7.37/1.47  --time_out_prep_mult                    0.1
% 7.37/1.47  --splitting_mode                        input
% 7.37/1.47  --splitting_grd                         true
% 7.37/1.47  --splitting_cvd                         false
% 7.37/1.47  --splitting_cvd_svl                     false
% 7.37/1.47  --splitting_nvd                         32
% 7.37/1.47  --sub_typing                            true
% 7.37/1.47  --prep_gs_sim                           true
% 7.37/1.47  --prep_unflatten                        true
% 7.37/1.47  --prep_res_sim                          true
% 7.37/1.47  --prep_upred                            true
% 7.37/1.47  --prep_sem_filter                       exhaustive
% 7.37/1.47  --prep_sem_filter_out                   false
% 7.37/1.47  --pred_elim                             true
% 7.37/1.47  --res_sim_input                         true
% 7.37/1.47  --eq_ax_congr_red                       true
% 7.37/1.47  --pure_diseq_elim                       true
% 7.37/1.47  --brand_transform                       false
% 7.37/1.47  --non_eq_to_eq                          false
% 7.37/1.47  --prep_def_merge                        true
% 7.37/1.47  --prep_def_merge_prop_impl              false
% 7.37/1.47  --prep_def_merge_mbd                    true
% 7.37/1.47  --prep_def_merge_tr_red                 false
% 7.37/1.47  --prep_def_merge_tr_cl                  false
% 7.37/1.47  --smt_preprocessing                     true
% 7.37/1.47  --smt_ac_axioms                         fast
% 7.37/1.47  --preprocessed_out                      false
% 7.37/1.47  --preprocessed_stats                    false
% 7.37/1.47  
% 7.37/1.47  ------ Abstraction refinement Options
% 7.37/1.47  
% 7.37/1.47  --abstr_ref                             []
% 7.37/1.47  --abstr_ref_prep                        false
% 7.37/1.47  --abstr_ref_until_sat                   false
% 7.37/1.47  --abstr_ref_sig_restrict                funpre
% 7.37/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.47  --abstr_ref_under                       []
% 7.37/1.47  
% 7.37/1.47  ------ SAT Options
% 7.37/1.47  
% 7.37/1.47  --sat_mode                              false
% 7.37/1.47  --sat_fm_restart_options                ""
% 7.37/1.47  --sat_gr_def                            false
% 7.37/1.47  --sat_epr_types                         true
% 7.37/1.47  --sat_non_cyclic_types                  false
% 7.37/1.47  --sat_finite_models                     false
% 7.37/1.47  --sat_fm_lemmas                         false
% 7.37/1.47  --sat_fm_prep                           false
% 7.37/1.47  --sat_fm_uc_incr                        true
% 7.37/1.47  --sat_out_model                         small
% 7.37/1.47  --sat_out_clauses                       false
% 7.37/1.47  
% 7.37/1.47  ------ QBF Options
% 7.37/1.47  
% 7.37/1.47  --qbf_mode                              false
% 7.37/1.47  --qbf_elim_univ                         false
% 7.37/1.47  --qbf_dom_inst                          none
% 7.37/1.47  --qbf_dom_pre_inst                      false
% 7.37/1.47  --qbf_sk_in                             false
% 7.37/1.47  --qbf_pred_elim                         true
% 7.37/1.47  --qbf_split                             512
% 7.37/1.47  
% 7.37/1.47  ------ BMC1 Options
% 7.37/1.47  
% 7.37/1.47  --bmc1_incremental                      false
% 7.37/1.47  --bmc1_axioms                           reachable_all
% 7.37/1.47  --bmc1_min_bound                        0
% 7.37/1.47  --bmc1_max_bound                        -1
% 7.37/1.47  --bmc1_max_bound_default                -1
% 7.37/1.47  --bmc1_symbol_reachability              true
% 7.37/1.47  --bmc1_property_lemmas                  false
% 7.37/1.47  --bmc1_k_induction                      false
% 7.37/1.47  --bmc1_non_equiv_states                 false
% 7.37/1.47  --bmc1_deadlock                         false
% 7.37/1.47  --bmc1_ucm                              false
% 7.37/1.47  --bmc1_add_unsat_core                   none
% 7.37/1.47  --bmc1_unsat_core_children              false
% 7.37/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.47  --bmc1_out_stat                         full
% 7.37/1.47  --bmc1_ground_init                      false
% 7.37/1.47  --bmc1_pre_inst_next_state              false
% 7.37/1.47  --bmc1_pre_inst_state                   false
% 7.37/1.47  --bmc1_pre_inst_reach_state             false
% 7.37/1.47  --bmc1_out_unsat_core                   false
% 7.37/1.47  --bmc1_aig_witness_out                  false
% 7.37/1.47  --bmc1_verbose                          false
% 7.37/1.47  --bmc1_dump_clauses_tptp                false
% 7.37/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.47  --bmc1_dump_file                        -
% 7.37/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.47  --bmc1_ucm_extend_mode                  1
% 7.37/1.47  --bmc1_ucm_init_mode                    2
% 7.37/1.47  --bmc1_ucm_cone_mode                    none
% 7.37/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.47  --bmc1_ucm_relax_model                  4
% 7.37/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.47  --bmc1_ucm_layered_model                none
% 7.37/1.47  --bmc1_ucm_max_lemma_size               10
% 7.37/1.47  
% 7.37/1.47  ------ AIG Options
% 7.37/1.47  
% 7.37/1.47  --aig_mode                              false
% 7.37/1.47  
% 7.37/1.47  ------ Instantiation Options
% 7.37/1.47  
% 7.37/1.47  --instantiation_flag                    true
% 7.37/1.47  --inst_sos_flag                         false
% 7.37/1.47  --inst_sos_phase                        true
% 7.37/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel_side                     num_symb
% 7.37/1.47  --inst_solver_per_active                1400
% 7.37/1.47  --inst_solver_calls_frac                1.
% 7.37/1.47  --inst_passive_queue_type               priority_queues
% 7.37/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.47  --inst_passive_queues_freq              [25;2]
% 7.37/1.47  --inst_dismatching                      true
% 7.37/1.47  --inst_eager_unprocessed_to_passive     true
% 7.37/1.47  --inst_prop_sim_given                   true
% 7.37/1.47  --inst_prop_sim_new                     false
% 7.37/1.47  --inst_subs_new                         false
% 7.37/1.47  --inst_eq_res_simp                      false
% 7.37/1.47  --inst_subs_given                       false
% 7.37/1.47  --inst_orphan_elimination               true
% 7.37/1.47  --inst_learning_loop_flag               true
% 7.37/1.47  --inst_learning_start                   3000
% 7.37/1.47  --inst_learning_factor                  2
% 7.37/1.47  --inst_start_prop_sim_after_learn       3
% 7.37/1.47  --inst_sel_renew                        solver
% 7.37/1.47  --inst_lit_activity_flag                true
% 7.37/1.47  --inst_restr_to_given                   false
% 7.37/1.47  --inst_activity_threshold               500
% 7.37/1.47  --inst_out_proof                        true
% 7.37/1.47  
% 7.37/1.47  ------ Resolution Options
% 7.37/1.47  
% 7.37/1.47  --resolution_flag                       true
% 7.37/1.47  --res_lit_sel                           adaptive
% 7.37/1.47  --res_lit_sel_side                      none
% 7.37/1.47  --res_ordering                          kbo
% 7.37/1.47  --res_to_prop_solver                    active
% 7.37/1.47  --res_prop_simpl_new                    false
% 7.37/1.47  --res_prop_simpl_given                  true
% 7.37/1.47  --res_passive_queue_type                priority_queues
% 7.37/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.47  --res_passive_queues_freq               [15;5]
% 7.37/1.47  --res_forward_subs                      full
% 7.37/1.47  --res_backward_subs                     full
% 7.37/1.47  --res_forward_subs_resolution           true
% 7.37/1.47  --res_backward_subs_resolution          true
% 7.37/1.47  --res_orphan_elimination                true
% 7.37/1.47  --res_time_limit                        2.
% 7.37/1.47  --res_out_proof                         true
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Options
% 7.37/1.47  
% 7.37/1.47  --superposition_flag                    true
% 7.37/1.47  --sup_passive_queue_type                priority_queues
% 7.37/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.47  --demod_completeness_check              fast
% 7.37/1.47  --demod_use_ground                      true
% 7.37/1.47  --sup_to_prop_solver                    passive
% 7.37/1.47  --sup_prop_simpl_new                    true
% 7.37/1.47  --sup_prop_simpl_given                  true
% 7.37/1.47  --sup_fun_splitting                     false
% 7.37/1.47  --sup_smt_interval                      50000
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Simplification Setup
% 7.37/1.47  
% 7.37/1.47  --sup_indices_passive                   []
% 7.37/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.47  --sup_full_bw                           [BwDemod]
% 7.37/1.47  --sup_immed_triv                        [TrivRules]
% 7.37/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.47  --sup_immed_bw_main                     []
% 7.37/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.47  
% 7.37/1.47  ------ Combination Options
% 7.37/1.47  
% 7.37/1.47  --comb_res_mult                         3
% 7.37/1.47  --comb_sup_mult                         2
% 7.37/1.47  --comb_inst_mult                        10
% 7.37/1.47  
% 7.37/1.47  ------ Debug Options
% 7.37/1.47  
% 7.37/1.47  --dbg_backtrace                         false
% 7.37/1.47  --dbg_dump_prop_clauses                 false
% 7.37/1.47  --dbg_dump_prop_clauses_file            -
% 7.37/1.47  --dbg_out_stat                          false
% 7.37/1.47  ------ Parsing...
% 7.37/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.37/1.47  ------ Proving...
% 7.37/1.47  ------ Problem Properties 
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  clauses                                 31
% 7.37/1.47  conjectures                             13
% 7.37/1.47  EPR                                     11
% 7.37/1.47  Horn                                    24
% 7.37/1.47  unary                                   15
% 7.37/1.47  binary                                  4
% 7.37/1.47  lits                                    128
% 7.37/1.47  lits eq                                 15
% 7.37/1.47  fd_pure                                 0
% 7.37/1.47  fd_pseudo                               0
% 7.37/1.47  fd_cond                                 0
% 7.37/1.47  fd_pseudo_cond                          1
% 7.37/1.47  AC symbols                              0
% 7.37/1.47  
% 7.37/1.47  ------ Schedule dynamic 5 is on 
% 7.37/1.47  
% 7.37/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  ------ 
% 7.37/1.47  Current options:
% 7.37/1.47  ------ 
% 7.37/1.47  
% 7.37/1.47  ------ Input Options
% 7.37/1.47  
% 7.37/1.47  --out_options                           all
% 7.37/1.47  --tptp_safe_out                         true
% 7.37/1.47  --problem_path                          ""
% 7.37/1.47  --include_path                          ""
% 7.37/1.47  --clausifier                            res/vclausify_rel
% 7.37/1.47  --clausifier_options                    --mode clausify
% 7.37/1.47  --stdin                                 false
% 7.37/1.47  --stats_out                             all
% 7.37/1.47  
% 7.37/1.47  ------ General Options
% 7.37/1.47  
% 7.37/1.47  --fof                                   false
% 7.37/1.47  --time_out_real                         305.
% 7.37/1.47  --time_out_virtual                      -1.
% 7.37/1.47  --symbol_type_check                     false
% 7.37/1.47  --clausify_out                          false
% 7.37/1.47  --sig_cnt_out                           false
% 7.37/1.47  --trig_cnt_out                          false
% 7.37/1.47  --trig_cnt_out_tolerance                1.
% 7.37/1.47  --trig_cnt_out_sk_spl                   false
% 7.37/1.47  --abstr_cl_out                          false
% 7.37/1.47  
% 7.37/1.47  ------ Global Options
% 7.37/1.47  
% 7.37/1.47  --schedule                              default
% 7.37/1.47  --add_important_lit                     false
% 7.37/1.47  --prop_solver_per_cl                    1000
% 7.37/1.47  --min_unsat_core                        false
% 7.37/1.47  --soft_assumptions                      false
% 7.37/1.47  --soft_lemma_size                       3
% 7.37/1.47  --prop_impl_unit_size                   0
% 7.37/1.47  --prop_impl_unit                        []
% 7.37/1.47  --share_sel_clauses                     true
% 7.37/1.47  --reset_solvers                         false
% 7.37/1.47  --bc_imp_inh                            [conj_cone]
% 7.37/1.47  --conj_cone_tolerance                   3.
% 7.37/1.47  --extra_neg_conj                        none
% 7.37/1.47  --large_theory_mode                     true
% 7.37/1.47  --prolific_symb_bound                   200
% 7.37/1.47  --lt_threshold                          2000
% 7.37/1.47  --clause_weak_htbl                      true
% 7.37/1.47  --gc_record_bc_elim                     false
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing Options
% 7.37/1.47  
% 7.37/1.47  --preprocessing_flag                    true
% 7.37/1.47  --time_out_prep_mult                    0.1
% 7.37/1.47  --splitting_mode                        input
% 7.37/1.47  --splitting_grd                         true
% 7.37/1.47  --splitting_cvd                         false
% 7.37/1.47  --splitting_cvd_svl                     false
% 7.37/1.47  --splitting_nvd                         32
% 7.37/1.47  --sub_typing                            true
% 7.37/1.47  --prep_gs_sim                           true
% 7.37/1.47  --prep_unflatten                        true
% 7.37/1.47  --prep_res_sim                          true
% 7.37/1.47  --prep_upred                            true
% 7.37/1.47  --prep_sem_filter                       exhaustive
% 7.37/1.47  --prep_sem_filter_out                   false
% 7.37/1.47  --pred_elim                             true
% 7.37/1.47  --res_sim_input                         true
% 7.37/1.47  --eq_ax_congr_red                       true
% 7.37/1.47  --pure_diseq_elim                       true
% 7.37/1.47  --brand_transform                       false
% 7.37/1.47  --non_eq_to_eq                          false
% 7.37/1.47  --prep_def_merge                        true
% 7.37/1.47  --prep_def_merge_prop_impl              false
% 7.37/1.47  --prep_def_merge_mbd                    true
% 7.37/1.47  --prep_def_merge_tr_red                 false
% 7.37/1.47  --prep_def_merge_tr_cl                  false
% 7.37/1.47  --smt_preprocessing                     true
% 7.37/1.47  --smt_ac_axioms                         fast
% 7.37/1.47  --preprocessed_out                      false
% 7.37/1.47  --preprocessed_stats                    false
% 7.37/1.47  
% 7.37/1.47  ------ Abstraction refinement Options
% 7.37/1.47  
% 7.37/1.47  --abstr_ref                             []
% 7.37/1.47  --abstr_ref_prep                        false
% 7.37/1.47  --abstr_ref_until_sat                   false
% 7.37/1.47  --abstr_ref_sig_restrict                funpre
% 7.37/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.37/1.47  --abstr_ref_under                       []
% 7.37/1.47  
% 7.37/1.47  ------ SAT Options
% 7.37/1.47  
% 7.37/1.47  --sat_mode                              false
% 7.37/1.47  --sat_fm_restart_options                ""
% 7.37/1.47  --sat_gr_def                            false
% 7.37/1.47  --sat_epr_types                         true
% 7.37/1.47  --sat_non_cyclic_types                  false
% 7.37/1.47  --sat_finite_models                     false
% 7.37/1.47  --sat_fm_lemmas                         false
% 7.37/1.47  --sat_fm_prep                           false
% 7.37/1.47  --sat_fm_uc_incr                        true
% 7.37/1.47  --sat_out_model                         small
% 7.37/1.47  --sat_out_clauses                       false
% 7.37/1.47  
% 7.37/1.47  ------ QBF Options
% 7.37/1.47  
% 7.37/1.47  --qbf_mode                              false
% 7.37/1.47  --qbf_elim_univ                         false
% 7.37/1.47  --qbf_dom_inst                          none
% 7.37/1.47  --qbf_dom_pre_inst                      false
% 7.37/1.47  --qbf_sk_in                             false
% 7.37/1.47  --qbf_pred_elim                         true
% 7.37/1.47  --qbf_split                             512
% 7.37/1.47  
% 7.37/1.47  ------ BMC1 Options
% 7.37/1.47  
% 7.37/1.47  --bmc1_incremental                      false
% 7.37/1.47  --bmc1_axioms                           reachable_all
% 7.37/1.47  --bmc1_min_bound                        0
% 7.37/1.47  --bmc1_max_bound                        -1
% 7.37/1.47  --bmc1_max_bound_default                -1
% 7.37/1.47  --bmc1_symbol_reachability              true
% 7.37/1.47  --bmc1_property_lemmas                  false
% 7.37/1.47  --bmc1_k_induction                      false
% 7.37/1.47  --bmc1_non_equiv_states                 false
% 7.37/1.47  --bmc1_deadlock                         false
% 7.37/1.47  --bmc1_ucm                              false
% 7.37/1.47  --bmc1_add_unsat_core                   none
% 7.37/1.47  --bmc1_unsat_core_children              false
% 7.37/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.37/1.47  --bmc1_out_stat                         full
% 7.37/1.47  --bmc1_ground_init                      false
% 7.37/1.47  --bmc1_pre_inst_next_state              false
% 7.37/1.47  --bmc1_pre_inst_state                   false
% 7.37/1.47  --bmc1_pre_inst_reach_state             false
% 7.37/1.47  --bmc1_out_unsat_core                   false
% 7.37/1.47  --bmc1_aig_witness_out                  false
% 7.37/1.47  --bmc1_verbose                          false
% 7.37/1.47  --bmc1_dump_clauses_tptp                false
% 7.37/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.37/1.47  --bmc1_dump_file                        -
% 7.37/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.37/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.37/1.47  --bmc1_ucm_extend_mode                  1
% 7.37/1.47  --bmc1_ucm_init_mode                    2
% 7.37/1.47  --bmc1_ucm_cone_mode                    none
% 7.37/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.37/1.47  --bmc1_ucm_relax_model                  4
% 7.37/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.37/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.37/1.47  --bmc1_ucm_layered_model                none
% 7.37/1.47  --bmc1_ucm_max_lemma_size               10
% 7.37/1.47  
% 7.37/1.47  ------ AIG Options
% 7.37/1.47  
% 7.37/1.47  --aig_mode                              false
% 7.37/1.47  
% 7.37/1.47  ------ Instantiation Options
% 7.37/1.47  
% 7.37/1.47  --instantiation_flag                    true
% 7.37/1.47  --inst_sos_flag                         false
% 7.37/1.47  --inst_sos_phase                        true
% 7.37/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.37/1.47  --inst_lit_sel_side                     none
% 7.37/1.47  --inst_solver_per_active                1400
% 7.37/1.47  --inst_solver_calls_frac                1.
% 7.37/1.47  --inst_passive_queue_type               priority_queues
% 7.37/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.37/1.47  --inst_passive_queues_freq              [25;2]
% 7.37/1.47  --inst_dismatching                      true
% 7.37/1.47  --inst_eager_unprocessed_to_passive     true
% 7.37/1.47  --inst_prop_sim_given                   true
% 7.37/1.47  --inst_prop_sim_new                     false
% 7.37/1.47  --inst_subs_new                         false
% 7.37/1.47  --inst_eq_res_simp                      false
% 7.37/1.47  --inst_subs_given                       false
% 7.37/1.47  --inst_orphan_elimination               true
% 7.37/1.47  --inst_learning_loop_flag               true
% 7.37/1.47  --inst_learning_start                   3000
% 7.37/1.47  --inst_learning_factor                  2
% 7.37/1.47  --inst_start_prop_sim_after_learn       3
% 7.37/1.47  --inst_sel_renew                        solver
% 7.37/1.47  --inst_lit_activity_flag                true
% 7.37/1.47  --inst_restr_to_given                   false
% 7.37/1.47  --inst_activity_threshold               500
% 7.37/1.47  --inst_out_proof                        true
% 7.37/1.47  
% 7.37/1.47  ------ Resolution Options
% 7.37/1.47  
% 7.37/1.47  --resolution_flag                       false
% 7.37/1.47  --res_lit_sel                           adaptive
% 7.37/1.47  --res_lit_sel_side                      none
% 7.37/1.47  --res_ordering                          kbo
% 7.37/1.47  --res_to_prop_solver                    active
% 7.37/1.47  --res_prop_simpl_new                    false
% 7.37/1.47  --res_prop_simpl_given                  true
% 7.37/1.47  --res_passive_queue_type                priority_queues
% 7.37/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.37/1.47  --res_passive_queues_freq               [15;5]
% 7.37/1.47  --res_forward_subs                      full
% 7.37/1.47  --res_backward_subs                     full
% 7.37/1.47  --res_forward_subs_resolution           true
% 7.37/1.47  --res_backward_subs_resolution          true
% 7.37/1.47  --res_orphan_elimination                true
% 7.37/1.47  --res_time_limit                        2.
% 7.37/1.47  --res_out_proof                         true
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Options
% 7.37/1.47  
% 7.37/1.47  --superposition_flag                    true
% 7.37/1.47  --sup_passive_queue_type                priority_queues
% 7.37/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.37/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.37/1.47  --demod_completeness_check              fast
% 7.37/1.47  --demod_use_ground                      true
% 7.37/1.47  --sup_to_prop_solver                    passive
% 7.37/1.47  --sup_prop_simpl_new                    true
% 7.37/1.47  --sup_prop_simpl_given                  true
% 7.37/1.47  --sup_fun_splitting                     false
% 7.37/1.47  --sup_smt_interval                      50000
% 7.37/1.47  
% 7.37/1.47  ------ Superposition Simplification Setup
% 7.37/1.47  
% 7.37/1.47  --sup_indices_passive                   []
% 7.37/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.37/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.37/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.47  --sup_full_bw                           [BwDemod]
% 7.37/1.47  --sup_immed_triv                        [TrivRules]
% 7.37/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.37/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.47  --sup_immed_bw_main                     []
% 7.37/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.37/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.37/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.37/1.47  
% 7.37/1.47  ------ Combination Options
% 7.37/1.47  
% 7.37/1.47  --comb_res_mult                         3
% 7.37/1.47  --comb_sup_mult                         2
% 7.37/1.47  --comb_inst_mult                        10
% 7.37/1.47  
% 7.37/1.47  ------ Debug Options
% 7.37/1.47  
% 7.37/1.47  --dbg_backtrace                         false
% 7.37/1.47  --dbg_dump_prop_clauses                 false
% 7.37/1.47  --dbg_dump_prop_clauses_file            -
% 7.37/1.47  --dbg_out_stat                          false
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  ------ Proving...
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  % SZS status Theorem for theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  fof(f16,conjecture,(
% 7.37/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f17,negated_conjecture,(
% 7.37/1.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.37/1.47    inference(negated_conjecture,[],[f16])).
% 7.37/1.47  
% 7.37/1.47  fof(f37,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f17])).
% 7.37/1.47  
% 7.37/1.47  fof(f38,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.37/1.47    inference(flattening,[],[f37])).
% 7.37/1.47  
% 7.37/1.47  fof(f49,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f48,plain,(
% 7.37/1.47    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f47,plain,(
% 7.37/1.47    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f46,plain,(
% 7.37/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f45,plain,(
% 7.37/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f44,plain,(
% 7.37/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.37/1.47    introduced(choice_axiom,[])).
% 7.37/1.47  
% 7.37/1.47  fof(f50,plain,(
% 7.37/1.47    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.37/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f49,f48,f47,f46,f45,f44])).
% 7.37/1.47  
% 7.37/1.47  fof(f79,plain,(
% 7.37/1.47    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f4,axiom,(
% 7.37/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f20,plain,(
% 7.37/1.47    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f4])).
% 7.37/1.47  
% 7.37/1.47  fof(f55,plain,(
% 7.37/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.37/1.47    inference(cnf_transformation,[],[f20])).
% 7.37/1.47  
% 7.37/1.47  fof(f86,plain,(
% 7.37/1.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f13,axiom,(
% 7.37/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f31,plain,(
% 7.37/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.37/1.47    inference(ennf_transformation,[],[f13])).
% 7.37/1.47  
% 7.37/1.47  fof(f32,plain,(
% 7.37/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.37/1.47    inference(flattening,[],[f31])).
% 7.37/1.47  
% 7.37/1.47  fof(f67,plain,(
% 7.37/1.47    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f32])).
% 7.37/1.47  
% 7.37/1.47  fof(f84,plain,(
% 7.37/1.47    v1_funct_1(sK5)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f83,plain,(
% 7.37/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f81,plain,(
% 7.37/1.47    v1_funct_1(sK4)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f14,axiom,(
% 7.37/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f33,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f14])).
% 7.37/1.47  
% 7.37/1.47  fof(f34,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.37/1.47    inference(flattening,[],[f33])).
% 7.37/1.47  
% 7.37/1.47  fof(f42,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.37/1.47    inference(nnf_transformation,[],[f34])).
% 7.37/1.47  
% 7.37/1.47  fof(f43,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.37/1.47    inference(flattening,[],[f42])).
% 7.37/1.47  
% 7.37/1.47  fof(f69,plain,(
% 7.37/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f43])).
% 7.37/1.47  
% 7.37/1.47  fof(f91,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(equality_resolution,[],[f69])).
% 7.37/1.47  
% 7.37/1.47  fof(f15,axiom,(
% 7.37/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f35,plain,(
% 7.37/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f15])).
% 7.37/1.47  
% 7.37/1.47  fof(f36,plain,(
% 7.37/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.37/1.47    inference(flattening,[],[f35])).
% 7.37/1.47  
% 7.37/1.47  fof(f71,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f36])).
% 7.37/1.47  
% 7.37/1.47  fof(f72,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f36])).
% 7.37/1.47  
% 7.37/1.47  fof(f73,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f36])).
% 7.37/1.47  
% 7.37/1.47  fof(f5,axiom,(
% 7.37/1.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f21,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f5])).
% 7.37/1.47  
% 7.37/1.47  fof(f56,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f21])).
% 7.37/1.47  
% 7.37/1.47  fof(f75,plain,(
% 7.37/1.47    ~v1_xboole_0(sK1)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f76,plain,(
% 7.37/1.47    ~v1_xboole_0(sK2)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f82,plain,(
% 7.37/1.47    v1_funct_2(sK4,sK2,sK1)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f78,plain,(
% 7.37/1.47    ~v1_xboole_0(sK3)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f85,plain,(
% 7.37/1.47    v1_funct_2(sK5,sK3,sK1)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f9,axiom,(
% 7.37/1.47    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f24,plain,(
% 7.37/1.47    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.37/1.47    inference(ennf_transformation,[],[f9])).
% 7.37/1.47  
% 7.37/1.47  fof(f25,plain,(
% 7.37/1.47    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.37/1.47    inference(flattening,[],[f24])).
% 7.37/1.47  
% 7.37/1.47  fof(f40,plain,(
% 7.37/1.47    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.37/1.47    inference(nnf_transformation,[],[f25])).
% 7.37/1.47  
% 7.37/1.47  fof(f60,plain,(
% 7.37/1.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f40])).
% 7.37/1.47  
% 7.37/1.47  fof(f80,plain,(
% 7.37/1.47    r1_subset_1(sK2,sK3)),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f1,axiom,(
% 7.37/1.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f39,plain,(
% 7.37/1.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.37/1.47    inference(nnf_transformation,[],[f1])).
% 7.37/1.47  
% 7.37/1.47  fof(f51,plain,(
% 7.37/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f39])).
% 7.37/1.47  
% 7.37/1.47  fof(f6,axiom,(
% 7.37/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f22,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f6])).
% 7.37/1.47  
% 7.37/1.47  fof(f57,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f22])).
% 7.37/1.47  
% 7.37/1.47  fof(f7,axiom,(
% 7.37/1.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f58,plain,(
% 7.37/1.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.37/1.47    inference(cnf_transformation,[],[f7])).
% 7.37/1.47  
% 7.37/1.47  fof(f3,axiom,(
% 7.37/1.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f54,plain,(
% 7.37/1.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f3])).
% 7.37/1.47  
% 7.37/1.47  fof(f2,axiom,(
% 7.37/1.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f19,plain,(
% 7.37/1.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.37/1.47    inference(ennf_transformation,[],[f2])).
% 7.37/1.47  
% 7.37/1.47  fof(f53,plain,(
% 7.37/1.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f19])).
% 7.37/1.47  
% 7.37/1.47  fof(f8,axiom,(
% 7.37/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.37/1.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.37/1.47  
% 7.37/1.47  fof(f23,plain,(
% 7.37/1.47    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.37/1.47    inference(ennf_transformation,[],[f8])).
% 7.37/1.47  
% 7.37/1.47  fof(f59,plain,(
% 7.37/1.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f23])).
% 7.37/1.47  
% 7.37/1.47  fof(f77,plain,(
% 7.37/1.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  fof(f68,plain,(
% 7.37/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(cnf_transformation,[],[f43])).
% 7.37/1.47  
% 7.37/1.47  fof(f92,plain,(
% 7.37/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.37/1.47    inference(equality_resolution,[],[f68])).
% 7.37/1.47  
% 7.37/1.47  fof(f87,plain,(
% 7.37/1.47    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.37/1.47    inference(cnf_transformation,[],[f50])).
% 7.37/1.47  
% 7.37/1.47  cnf(c_31,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.37/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_838,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1636,plain,
% 7.37/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.37/1.47      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f55]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_855,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.37/1.47      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_4]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1620,plain,
% 7.37/1.47      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2294,plain,
% 7.37/1.47      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1636,c_1620]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_24,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.37/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_844,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_24]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1630,plain,
% 7.37/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_16,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.37/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_850,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.37/1.47      | ~ v1_funct_1(X0_53)
% 7.37/1.47      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_16]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1625,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3052,plain,
% 7.37/1.47      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.37/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1630,c_1625]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_26,negated_conjecture,
% 7.37/1.47      ( v1_funct_1(sK5) ),
% 7.37/1.47      inference(cnf_transformation,[],[f84]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2058,plain,
% 7.37/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.37/1.47      | ~ v1_funct_1(sK5)
% 7.37/1.47      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_850]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2236,plain,
% 7.37/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.37/1.47      | ~ v1_funct_1(sK5)
% 7.37/1.47      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2058]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3283,plain,
% 7.37/1.47      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_3052,c_26,c_24,c_2236]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_27,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.37/1.47      inference(cnf_transformation,[],[f83]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_841,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_27]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1633,plain,
% 7.37/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3053,plain,
% 7.37/1.47      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.37/1.47      | v1_funct_1(sK4) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1633,c_1625]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_29,negated_conjecture,
% 7.37/1.47      ( v1_funct_1(sK4) ),
% 7.37/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2063,plain,
% 7.37/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.37/1.47      | ~ v1_funct_1(sK4)
% 7.37/1.47      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_850]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2241,plain,
% 7.37/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.37/1.47      | ~ v1_funct_1(sK4)
% 7.37/1.47      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_2063]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3646,plain,
% 7.37/1.47      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_3053,c_29,c_27,c_2241]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_18,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.37/1.47      inference(cnf_transformation,[],[f91]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_22,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_21,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_20,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_205,plain,
% 7.37/1.47      ( ~ v1_funct_1(X3)
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_18,c_22,c_21,c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_206,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_205]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_831,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.37/1.47      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.37/1.47      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.37/1.47      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.37/1.47      | ~ v1_funct_1(X0_53)
% 7.37/1.47      | ~ v1_funct_1(X3_53)
% 7.37/1.47      | v1_xboole_0(X2_53)
% 7.37/1.47      | v1_xboole_0(X1_53)
% 7.37/1.47      | v1_xboole_0(X4_53)
% 7.37/1.47      | v1_xboole_0(X5_53)
% 7.37/1.47      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_206]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1643,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.37/1.47      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X5_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X3_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.37/1.47      | ~ v1_xboole_0(X1)
% 7.37/1.47      | v1_xboole_0(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_854,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.37/1.47      | ~ v1_xboole_0(X1_53)
% 7.37/1.47      | v1_xboole_0(X0_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_5]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1621,plain,
% 7.37/1.47      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1854,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
% 7.37/1.47      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X5_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top ),
% 7.37/1.47      inference(forward_subsumption_resolution,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1643,c_1621]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7341,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.37/1.47      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.37/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(X1_53) != iProver_top
% 7.37/1.47      | v1_funct_1(sK4) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.37/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3646,c_1854]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_35,negated_conjecture,
% 7.37/1.47      ( ~ v1_xboole_0(sK1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_38,plain,
% 7.37/1.47      ( v1_xboole_0(sK1) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_34,negated_conjecture,
% 7.37/1.47      ( ~ v1_xboole_0(sK2) ),
% 7.37/1.47      inference(cnf_transformation,[],[f76]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_39,plain,
% 7.37/1.47      ( v1_xboole_0(sK2) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_44,plain,
% 7.37/1.47      ( v1_funct_1(sK4) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_28,negated_conjecture,
% 7.37/1.47      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f82]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_45,plain,
% 7.37/1.47      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_46,plain,
% 7.37/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17426,plain,
% 7.37/1.47      ( v1_funct_1(X1_53) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.37/1.47      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.37/1.47      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_7341,c_38,c_39,c_44,c_45,c_46]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17427,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.37/1.47      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(X1_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_17426]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17440,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
% 7.37/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(sK5) != iProver_top
% 7.37/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3283,c_17427]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_32,negated_conjecture,
% 7.37/1.47      ( ~ v1_xboole_0(sK3) ),
% 7.37/1.47      inference(cnf_transformation,[],[f78]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_41,plain,
% 7.37/1.47      ( v1_xboole_0(sK3) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_47,plain,
% 7.37/1.47      ( v1_funct_1(sK5) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_25,negated_conjecture,
% 7.37/1.47      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f85]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_48,plain,
% 7.37/1.47      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_49,plain,
% 7.37/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17781,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_17440,c_41,c_47,c_48,c_49]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17791,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_2294,c_17781]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_10,plain,
% 7.37/1.47      ( ~ r1_subset_1(X0,X1)
% 7.37/1.47      | r1_xboole_0(X0,X1)
% 7.37/1.47      | v1_xboole_0(X0)
% 7.37/1.47      | v1_xboole_0(X1) ),
% 7.37/1.47      inference(cnf_transformation,[],[f60]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_30,negated_conjecture,
% 7.37/1.47      ( r1_subset_1(sK2,sK3) ),
% 7.37/1.47      inference(cnf_transformation,[],[f80]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_508,plain,
% 7.37/1.47      ( r1_xboole_0(X0,X1)
% 7.37/1.47      | v1_xboole_0(X0)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | sK3 != X1
% 7.37/1.47      | sK2 != X0 ),
% 7.37/1.47      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_509,plain,
% 7.37/1.47      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.37/1.47      inference(unflattening,[status(thm)],[c_508]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_511,plain,
% 7.37/1.47      ( r1_xboole_0(sK2,sK3) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_509,c_34,c_32]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_830,plain,
% 7.37/1.47      ( r1_xboole_0(sK2,sK3) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_511]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1644,plain,
% 7.37/1.47      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1,plain,
% 7.37/1.47      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.37/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_858,plain,
% 7.37/1.47      ( ~ r1_xboole_0(X0_53,X1_53)
% 7.37/1.47      | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_1]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1617,plain,
% 7.37/1.47      ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
% 7.37/1.47      | r1_xboole_0(X0_53,X1_53) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2665,plain,
% 7.37/1.47      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1644,c_1617]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_6,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.37/1.47      | ~ v1_relat_1(X1)
% 7.37/1.47      | v1_relat_1(X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f57]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_853,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.37/1.47      | ~ v1_relat_1(X1_53)
% 7.37/1.47      | v1_relat_1(X0_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_6]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1622,plain,
% 7.37/1.47      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.37/1.47      | v1_relat_1(X1_53) != iProver_top
% 7.37/1.47      | v1_relat_1(X0_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2717,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.37/1.47      | v1_relat_1(sK5) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1630,c_1622]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1973,plain,
% 7.37/1.47      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.37/1.47      | v1_relat_1(X0_53)
% 7.37/1.47      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_853]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2414,plain,
% 7.37/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.37/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 7.37/1.47      | v1_relat_1(sK5) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_1973]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2415,plain,
% 7.37/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.37/1.47      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.37/1.47      | v1_relat_1(sK5) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_2414]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.37/1.47      inference(cnf_transformation,[],[f58]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_852,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_7]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2531,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_852]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2532,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_2531]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2924,plain,
% 7.37/1.47      ( v1_relat_1(sK5) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_2717,c_49,c_2415,c_2532]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3,plain,
% 7.37/1.47      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_856,plain,
% 7.37/1.47      ( r1_xboole_0(X0_53,k1_xboole_0) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_3]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1619,plain,
% 7.37/1.47      ( r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2,plain,
% 7.37/1.47      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.37/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_857,plain,
% 7.37/1.47      ( ~ r1_xboole_0(X0_53,X1_53) | r1_xboole_0(X1_53,X0_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_2]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1618,plain,
% 7.37/1.47      ( r1_xboole_0(X0_53,X1_53) != iProver_top
% 7.37/1.47      | r1_xboole_0(X1_53,X0_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2704,plain,
% 7.37/1.47      ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1619,c_1618]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8,plain,
% 7.37/1.47      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.37/1.47      | ~ v1_relat_1(X1)
% 7.37/1.47      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.37/1.47      inference(cnf_transformation,[],[f59]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_851,plain,
% 7.37/1.47      ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
% 7.37/1.47      | ~ v1_relat_1(X1_53)
% 7.37/1.47      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_8]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1624,plain,
% 7.37/1.47      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.37/1.47      | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
% 7.37/1.47      | v1_relat_1(X0_53) != iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3271,plain,
% 7.37/1.47      ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
% 7.37/1.47      | v1_relat_1(X0_53) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_2704,c_1624]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3811,plain,
% 7.37/1.47      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_2924,c_3271]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17792,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(light_normalisation,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_17791,c_2665,c_3811]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_848,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.37/1.47      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.37/1.47      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.37/1.47      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.37/1.47      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 7.37/1.47      | ~ v1_funct_1(X0_53)
% 7.37/1.47      | ~ v1_funct_1(X3_53)
% 7.37/1.47      | v1_xboole_0(X2_53)
% 7.37/1.47      | v1_xboole_0(X1_53)
% 7.37/1.47      | v1_xboole_0(X4_53)
% 7.37/1.47      | v1_xboole_0(X5_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1627,plain,
% 7.37/1.47      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.37/1.47      | v1_funct_1(X0_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X3_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X5_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X2_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1799,plain,
% 7.37/1.47      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.37/1.47      | v1_funct_1(X0_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X3_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X2_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top ),
% 7.37/1.47      inference(forward_subsumption_resolution,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1627,c_1621]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4906,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.37/1.47      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X5_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X4_53) != iProver_top
% 7.37/1.47      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 7.37/1.47      | v1_xboole_0(X3_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X2_53) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1799,c_1625]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_846,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.37/1.47      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.37/1.47      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.37/1.47      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.37/1.47      | ~ v1_funct_1(X0_53)
% 7.37/1.47      | ~ v1_funct_1(X3_53)
% 7.37/1.47      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 7.37/1.47      | v1_xboole_0(X2_53)
% 7.37/1.47      | v1_xboole_0(X1_53)
% 7.37/1.47      | v1_xboole_0(X4_53)
% 7.37/1.47      | v1_xboole_0(X5_53) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_22]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1629,plain,
% 7.37/1.47      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X0_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X3_53) != iProver_top
% 7.37/1.47      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.37/1.47      | v1_xboole_0(X5_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X2_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1747,plain,
% 7.37/1.47      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X0_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X3_53) != iProver_top
% 7.37/1.47      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.37/1.47      | v1_xboole_0(X2_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top ),
% 7.37/1.47      inference(forward_subsumption_resolution,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1629,c_1621]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7971,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.37/1.47      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X5_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X4_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X2_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X3_53) = iProver_top ),
% 7.37/1.47      inference(forward_subsumption_resolution,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_4906,c_1747]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_7975,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.37/1.47      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.37/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | v1_funct_1(sK5) != iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.37/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1630,c_7971]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8074,plain,
% 7.37/1.47      ( v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.37/1.47      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_7975,c_38,c_41,c_47,c_48]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8075,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.37/1.47      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_8074]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8088,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.37/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(sK4) != iProver_top
% 7.37/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1633,c_8075]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8479,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_8088,c_39,c_44,c_45]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8488,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1636,c_8479]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_33,negated_conjecture,
% 7.37/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.37/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_40,plain,
% 7.37/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8493,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_8488,c_40]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17793,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_17792,c_2294,c_8493]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2718,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.37/1.47      | v1_relat_1(sK4) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_1633,c_1622]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2417,plain,
% 7.37/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.37/1.47      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 7.37/1.47      | v1_relat_1(sK4) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_1973]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2418,plain,
% 7.37/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.37/1.47      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.37/1.47      | v1_relat_1(sK4) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_2417]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2534,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 7.37/1.47      inference(instantiation,[status(thm)],[c_852]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2535,plain,
% 7.37/1.47      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_2534]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2991,plain,
% 7.37/1.47      ( v1_relat_1(sK4) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_2718,c_46,c_2418,c_2535]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3812,plain,
% 7.37/1.47      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_2991,c_3271]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17794,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | k1_xboole_0 != k1_xboole_0
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(light_normalisation,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_17793,c_2665,c_3812]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_17795,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(equality_resolution_simp,[status(thm)],[c_17794]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_19,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.37/1.47      inference(cnf_transformation,[],[f92]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_198,plain,
% 7.37/1.47      ( ~ v1_funct_1(X3)
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_19,c_22,c_21,c_20]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_199,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.37/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.37/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.37/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.37/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.37/1.47      | ~ v1_funct_1(X0)
% 7.37/1.47      | ~ v1_funct_1(X3)
% 7.37/1.47      | v1_xboole_0(X1)
% 7.37/1.47      | v1_xboole_0(X2)
% 7.37/1.47      | v1_xboole_0(X4)
% 7.37/1.47      | v1_xboole_0(X5)
% 7.37/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_198]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_832,plain,
% 7.37/1.47      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.37/1.47      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.37/1.47      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.37/1.47      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.37/1.47      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.37/1.47      | ~ v1_funct_1(X0_53)
% 7.37/1.47      | ~ v1_funct_1(X3_53)
% 7.37/1.47      | v1_xboole_0(X2_53)
% 7.37/1.47      | v1_xboole_0(X1_53)
% 7.37/1.47      | v1_xboole_0(X4_53)
% 7.37/1.47      | v1_xboole_0(X5_53)
% 7.37/1.47      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_199]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1642,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.37/1.47      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X5_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X3_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_1826,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
% 7.37/1.47      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.37/1.47      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.37/1.47      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.37/1.47      | v1_funct_1(X5_53) != iProver_top
% 7.37/1.47      | v1_funct_1(X2_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X1_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(X4_53) = iProver_top ),
% 7.37/1.47      inference(forward_subsumption_resolution,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_1642,c_1621]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_5257,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.37/1.47      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.37/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(X1_53) != iProver_top
% 7.37/1.47      | v1_funct_1(sK4) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top
% 7.37/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.37/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3646,c_1826]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_14963,plain,
% 7.37/1.47      ( v1_funct_1(X1_53) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.37/1.47      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.37/1.47      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_5257,c_38,c_39,c_44,c_45,c_46]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_14964,plain,
% 7.37/1.47      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.37/1.47      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.37/1.47      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(X1_53) != iProver_top
% 7.37/1.47      | v1_xboole_0(X0_53) = iProver_top ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_14963]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_14977,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
% 7.37/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.37/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | v1_funct_1(sK5) != iProver_top
% 7.37/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_3283,c_14964]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15335,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_14977,c_41,c_47,c_48,c_49]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15345,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(superposition,[status(thm)],[c_2294,c_15335]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15346,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(light_normalisation,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_15345,c_2665,c_3811]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15347,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_15346,c_2294,c_8493]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15348,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | k1_xboole_0 != k1_xboole_0
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(light_normalisation,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_15347,c_2665,c_3812]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_15349,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.37/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.37/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.37/1.47      inference(equality_resolution_simp,[status(thm)],[c_15348]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_23,negated_conjecture,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.37/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_845,negated_conjecture,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.37/1.47      inference(subtyping,[status(esa)],[c_23]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2474,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_2294,c_845]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_2997,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_2665,c_2474]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3650,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_2997,c_3283,c_3646]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_3821,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_3811,c_3650]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4587,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.37/1.47      inference(global_propositional_subsumption,
% 7.37/1.47                [status(thm)],
% 7.37/1.47                [c_3821,c_3812]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_4588,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.37/1.47      inference(renaming,[status(thm)],[c_4587]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8497,plain,
% 7.37/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.37/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_8493,c_4588]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_8498,plain,
% 7.37/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.37/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.37/1.47      inference(demodulation,[status(thm)],[c_8497,c_8493]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(c_42,plain,
% 7.37/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.37/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.37/1.47  
% 7.37/1.47  cnf(contradiction,plain,
% 7.37/1.47      ( $false ),
% 7.37/1.47      inference(minisat,[status(thm)],[c_17795,c_15349,c_8498,c_42,c_40]) ).
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.37/1.47  
% 7.37/1.47  ------                               Statistics
% 7.37/1.47  
% 7.37/1.47  ------ General
% 7.37/1.47  
% 7.37/1.47  abstr_ref_over_cycles:                  0
% 7.37/1.47  abstr_ref_under_cycles:                 0
% 7.37/1.47  gc_basic_clause_elim:                   0
% 7.37/1.47  forced_gc_time:                         0
% 7.37/1.47  parsing_time:                           0.01
% 7.37/1.47  unif_index_cands_time:                  0.
% 7.37/1.47  unif_index_add_time:                    0.
% 7.37/1.47  orderings_time:                         0.
% 7.37/1.47  out_proof_time:                         0.019
% 7.37/1.47  total_time:                             0.984
% 7.37/1.47  num_of_symbols:                         58
% 7.37/1.47  num_of_terms:                           32404
% 7.37/1.47  
% 7.37/1.47  ------ Preprocessing
% 7.37/1.47  
% 7.37/1.47  num_of_splits:                          0
% 7.37/1.47  num_of_split_atoms:                     0
% 7.37/1.47  num_of_reused_defs:                     0
% 7.37/1.47  num_eq_ax_congr_red:                    18
% 7.37/1.47  num_of_sem_filtered_clauses:            1
% 7.37/1.47  num_of_subtypes:                        2
% 7.37/1.47  monotx_restored_types:                  0
% 7.37/1.47  sat_num_of_epr_types:                   0
% 7.37/1.47  sat_num_of_non_cyclic_types:            0
% 7.37/1.47  sat_guarded_non_collapsed_types:        1
% 7.37/1.47  num_pure_diseq_elim:                    0
% 7.37/1.47  simp_replaced_by:                       0
% 7.37/1.47  res_preprocessed:                       160
% 7.37/1.47  prep_upred:                             0
% 7.37/1.47  prep_unflattend:                        6
% 7.37/1.47  smt_new_axioms:                         0
% 7.37/1.47  pred_elim_cands:                        6
% 7.37/1.47  pred_elim:                              3
% 7.37/1.47  pred_elim_cl:                           5
% 7.37/1.47  pred_elim_cycles:                       6
% 7.37/1.47  merged_defs:                            8
% 7.37/1.47  merged_defs_ncl:                        0
% 7.37/1.47  bin_hyper_res:                          8
% 7.37/1.47  prep_cycles:                            4
% 7.37/1.47  pred_elim_time:                         0.004
% 7.37/1.47  splitting_time:                         0.
% 7.37/1.47  sem_filter_time:                        0.
% 7.37/1.47  monotx_time:                            0.
% 7.37/1.47  subtype_inf_time:                       0.002
% 7.37/1.47  
% 7.37/1.47  ------ Problem properties
% 7.37/1.47  
% 7.37/1.47  clauses:                                31
% 7.37/1.47  conjectures:                            13
% 7.37/1.47  epr:                                    11
% 7.37/1.47  horn:                                   24
% 7.37/1.47  ground:                                 14
% 7.37/1.47  unary:                                  15
% 7.37/1.47  binary:                                 4
% 7.37/1.47  lits:                                   128
% 7.37/1.47  lits_eq:                                15
% 7.37/1.47  fd_pure:                                0
% 7.37/1.47  fd_pseudo:                              0
% 7.37/1.47  fd_cond:                                0
% 7.37/1.47  fd_pseudo_cond:                         1
% 7.37/1.47  ac_symbols:                             0
% 7.37/1.47  
% 7.37/1.47  ------ Propositional Solver
% 7.37/1.47  
% 7.37/1.47  prop_solver_calls:                      30
% 7.37/1.47  prop_fast_solver_calls:                 2432
% 7.37/1.47  smt_solver_calls:                       0
% 7.37/1.47  smt_fast_solver_calls:                  0
% 7.37/1.47  prop_num_of_clauses:                    7074
% 7.37/1.47  prop_preprocess_simplified:             16022
% 7.37/1.47  prop_fo_subsumed:                       207
% 7.37/1.47  prop_solver_time:                       0.
% 7.37/1.47  smt_solver_time:                        0.
% 7.37/1.47  smt_fast_solver_time:                   0.
% 7.37/1.47  prop_fast_solver_time:                  0.
% 7.37/1.47  prop_unsat_core_time:                   0.001
% 7.37/1.47  
% 7.37/1.47  ------ QBF
% 7.37/1.47  
% 7.37/1.47  qbf_q_res:                              0
% 7.37/1.47  qbf_num_tautologies:                    0
% 7.37/1.47  qbf_prep_cycles:                        0
% 7.37/1.47  
% 7.37/1.47  ------ BMC1
% 7.37/1.47  
% 7.37/1.47  bmc1_current_bound:                     -1
% 7.37/1.47  bmc1_last_solved_bound:                 -1
% 7.37/1.47  bmc1_unsat_core_size:                   -1
% 7.37/1.47  bmc1_unsat_core_parents_size:           -1
% 7.37/1.47  bmc1_merge_next_fun:                    0
% 7.37/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.37/1.47  
% 7.37/1.47  ------ Instantiation
% 7.37/1.47  
% 7.37/1.47  inst_num_of_clauses:                    1716
% 7.37/1.47  inst_num_in_passive:                    796
% 7.37/1.47  inst_num_in_active:                     747
% 7.37/1.47  inst_num_in_unprocessed:                173
% 7.37/1.47  inst_num_of_loops:                      760
% 7.37/1.47  inst_num_of_learning_restarts:          0
% 7.37/1.47  inst_num_moves_active_passive:          9
% 7.37/1.47  inst_lit_activity:                      0
% 7.37/1.47  inst_lit_activity_moves:                0
% 7.37/1.47  inst_num_tautologies:                   0
% 7.37/1.47  inst_num_prop_implied:                  0
% 7.37/1.47  inst_num_existing_simplified:           0
% 7.37/1.47  inst_num_eq_res_simplified:             0
% 7.37/1.47  inst_num_child_elim:                    0
% 7.37/1.47  inst_num_of_dismatching_blockings:      122
% 7.37/1.47  inst_num_of_non_proper_insts:           1359
% 7.37/1.47  inst_num_of_duplicates:                 0
% 7.37/1.47  inst_inst_num_from_inst_to_res:         0
% 7.37/1.47  inst_dismatching_checking_time:         0.
% 7.37/1.47  
% 7.37/1.47  ------ Resolution
% 7.37/1.47  
% 7.37/1.47  res_num_of_clauses:                     0
% 7.37/1.47  res_num_in_passive:                     0
% 7.37/1.47  res_num_in_active:                      0
% 7.37/1.47  res_num_of_loops:                       164
% 7.37/1.47  res_forward_subset_subsumed:            45
% 7.37/1.47  res_backward_subset_subsumed:           2
% 7.37/1.47  res_forward_subsumed:                   0
% 7.37/1.47  res_backward_subsumed:                  0
% 7.37/1.47  res_forward_subsumption_resolution:     0
% 7.37/1.47  res_backward_subsumption_resolution:    0
% 7.37/1.47  res_clause_to_clause_subsumption:       1361
% 7.37/1.47  res_orphan_elimination:                 0
% 7.37/1.47  res_tautology_del:                      50
% 7.37/1.47  res_num_eq_res_simplified:              0
% 7.37/1.47  res_num_sel_changes:                    0
% 7.37/1.47  res_moves_from_active_to_pass:          0
% 7.37/1.47  
% 7.37/1.47  ------ Superposition
% 7.37/1.47  
% 7.37/1.47  sup_time_total:                         0.
% 7.37/1.47  sup_time_generating:                    0.
% 7.37/1.47  sup_time_sim_full:                      0.
% 7.37/1.47  sup_time_sim_immed:                     0.
% 7.37/1.47  
% 7.37/1.47  sup_num_of_clauses:                     271
% 7.37/1.47  sup_num_in_active:                      145
% 7.37/1.47  sup_num_in_passive:                     126
% 7.37/1.47  sup_num_of_loops:                       150
% 7.37/1.47  sup_fw_superposition:                   254
% 7.37/1.47  sup_bw_superposition:                   51
% 7.37/1.47  sup_immediate_simplified:               132
% 7.37/1.47  sup_given_eliminated:                   0
% 7.37/1.47  comparisons_done:                       0
% 7.37/1.47  comparisons_avoided:                    0
% 7.37/1.47  
% 7.37/1.47  ------ Simplifications
% 7.37/1.47  
% 7.37/1.47  
% 7.37/1.47  sim_fw_subset_subsumed:                 8
% 7.37/1.47  sim_bw_subset_subsumed:                 3
% 7.37/1.47  sim_fw_subsumed:                        10
% 7.37/1.47  sim_bw_subsumed:                        8
% 7.37/1.47  sim_fw_subsumption_res:                 11
% 7.37/1.47  sim_bw_subsumption_res:                 0
% 7.37/1.47  sim_tautology_del:                      0
% 7.37/1.47  sim_eq_tautology_del:                   2
% 7.37/1.47  sim_eq_res_simp:                        8
% 7.37/1.47  sim_fw_demodulated:                     74
% 7.37/1.47  sim_bw_demodulated:                     5
% 7.37/1.47  sim_light_normalised:                   55
% 7.37/1.47  sim_joinable_taut:                      0
% 7.37/1.47  sim_joinable_simp:                      0
% 7.37/1.47  sim_ac_normalised:                      0
% 7.37/1.47  sim_smt_subsumption:                    0
% 7.37/1.47  
%------------------------------------------------------------------------------
