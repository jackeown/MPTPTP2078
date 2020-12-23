%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:31 EST 2020

% Result     : Theorem 15.28s
% Output     : CNFRefutation 15.28s
% Verified   : 
% Statistics : Number of formulae       :  241 (2446 expanded)
%              Number of clauses        :  161 ( 598 expanded)
%              Number of leaves         :   21 ( 967 expanded)
%              Depth                    :   27
%              Number of atoms          : 1241 (32296 expanded)
%              Number of equality atoms :  439 (7481 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f49,f48,f47,f46,f45,f44])).

fof(f78,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f35])).

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

fof(f66,plain,(
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

fof(f90,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f69,plain,(
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

fof(f70,plain,(
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

fof(f71,plain,(
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

fof(f83,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f67,plain,(
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

fof(f89,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_461,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1088,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_479,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_subset_1(X1_53,X0_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1071,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_subset_1(X1_53,X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_3797,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1071])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_41,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1518,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ r1_subset_1(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_479])).

cnf(c_1519,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_4359,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_37,c_39,c_41,c_1519])).

cnf(c_6,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_480,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_xboole_0(X0_53,X1_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1070,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X0_53,X1_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_4365,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4359,c_1070])).

cnf(c_1745,plain,
    ( ~ r1_subset_1(sK3,sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1747,plain,
    ( r1_subset_1(sK3,sK2) != iProver_top
    | r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1745])).

cnf(c_4374,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4365,c_37,c_39,c_41,c_1519,c_1747])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_464,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1085,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_476,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | v1_partfun1(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1074,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_partfun1(X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_5534,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1074])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1618,plain,
    ( ~ v1_funct_2(sK4,X0_53,X1_53)
    | v1_partfun1(sK4,X0_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_1890,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1618])).

cnf(c_1891,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_6050,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5534,c_36,c_42,c_43,c_44,c_1891])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_474,plain,
    ( ~ v1_partfun1(X0_53,X1_53)
    | ~ v4_relat_1(X0_53,X1_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1076,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_partfun1(X0_53,X1_53) != iProver_top
    | v4_relat_1(X0_53,X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_24483,plain,
    ( k1_relat_1(sK4) = sK2
    | v4_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6050,c_1076])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1483,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_477,plain,
    ( v4_relat_1(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1515,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1722,plain,
    ( ~ v1_partfun1(sK4,X0_53)
    | ~ v4_relat_1(sK4,X0_53)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1729,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1722])).

cnf(c_24500,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24483,c_33,c_27,c_26,c_25,c_1483,c_1515,c_1729,c_1890])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_483,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1067,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_24673,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_24500,c_1067])).

cnf(c_1484,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1483])).

cnf(c_41808,plain,
    ( r1_xboole_0(X0_53,sK2) != iProver_top
    | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24673,c_44,c_1484])).

cnf(c_41809,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_41808])).

cnf(c_41816,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4374,c_41809])).

cnf(c_1072,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_2212,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1072])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_482,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1068,plain,
    ( k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_2396,plain,
    ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_53)) = k7_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_2212,c_1068])).

cnf(c_24549,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_53)) = k7_relat_1(sK4,X0_53) ),
    inference(demodulation,[status(thm)],[c_24500,c_2396])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_460,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1089,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1065,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_1843,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1089,c_1065])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_473,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1077,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_6730,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1085,c_1077])).

cnf(c_1592,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1882,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_7299,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6730,c_27,c_25,c_1882])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_467,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1082,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_6729,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1077])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1587,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_1877,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_7293,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6729,c_24,c_22,c_1877])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f90])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_274,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_20,c_19,c_18])).

cnf(c_275,plain,
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
    inference(renaming,[status(thm)],[c_274])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_275])).

cnf(c_1096,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_21402,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7293,c_1096])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_27275,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21402,c_36,c_39,c_45,c_46,c_47])).

cnf(c_27276,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_27275])).

cnf(c_27291,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7299,c_27276])).

cnf(c_27337,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27291,c_37,c_42,c_43,c_44])).

cnf(c_27338,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_27337])).

cnf(c_27348,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_27338])).

cnf(c_27349,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_27348,c_1843])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_468,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2036,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1843,c_468])).

cnf(c_7297,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_7293,c_2036])).

cnf(c_7385,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_7297,c_7299])).

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
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | v1_xboole_0(X1)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_265,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_20,c_19,c_18])).

cnf(c_266,plain,
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
    inference(renaming,[status(thm)],[c_265])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_266])).

cnf(c_1095,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_19103,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7293,c_1095])).

cnf(c_20519,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19103,c_36,c_39,c_45,c_46,c_47])).

cnf(c_20520,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_20519])).

cnf(c_20535,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7299,c_20520])).

cnf(c_20859,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20535,c_37,c_42,c_43,c_44])).

cnf(c_20860,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_20859])).

cnf(c_20870,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1843,c_20860])).

cnf(c_20871,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20870,c_1843])).

cnf(c_20872,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20871])).

cnf(c_20874,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20871,c_34,c_31,c_29,c_20872])).

cnf(c_20875,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_20874])).

cnf(c_27350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_27349])).

cnf(c_27553,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27349,c_34,c_31,c_29,c_7385,c_20875,c_27350])).

cnf(c_33063,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_24549,c_27553])).

cnf(c_5533,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1074])).

cnf(c_1613,plain,
    ( ~ v1_funct_2(sK5,X0_53,X1_53)
    | v1_partfun1(sK5,X0_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_53) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_1887,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_1888,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1887])).

cnf(c_5978,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5533,c_36,c_45,c_46,c_47,c_1888])).

cnf(c_24484,plain,
    ( k1_relat_1(sK5) = sK3
    | v4_relat_1(sK5,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5978,c_1076])).

cnf(c_1480,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_1512,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_1707,plain,
    ( ~ v1_partfun1(sK5,X0_53)
    | ~ v4_relat_1(sK5,X0_53)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_2177,plain,
    ( ~ v1_partfun1(sK5,sK3)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_24788,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_24484,c_33,c_24,c_23,c_22,c_1480,c_1512,c_1887,c_2177])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_486,plain,
    ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2211,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1082,c_1072])).

cnf(c_2386,plain,
    ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_53)) = k7_relat_1(sK5,X0_53) ),
    inference(superposition,[status(thm)],[c_2211,c_1068])).

cnf(c_2683,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_53,k1_relat_1(sK5))) = k7_relat_1(sK5,X0_53) ),
    inference(superposition,[status(thm)],[c_486,c_2386])).

cnf(c_24838,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_53,sK3)) = k7_relat_1(sK5,X0_53) ),
    inference(demodulation,[status(thm)],[c_24788,c_2683])).

cnf(c_33752,plain,
    ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) ),
    inference(demodulation,[status(thm)],[c_33063,c_24838])).

cnf(c_41818,plain,
    ( k7_relat_1(sK5,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_41816,c_33752])).

cnf(c_4339,plain,
    ( ~ r1_xboole_0(sK2,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_483])).

cnf(c_496,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(X0_53,X2_53)
    | X2_53 != X1_53 ),
    theory(equality)).

cnf(c_1754,plain,
    ( r1_xboole_0(sK2,X0_53)
    | ~ r1_xboole_0(sK2,sK3)
    | X0_53 != sK3 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_2871,plain,
    ( r1_xboole_0(sK2,k1_relat_1(sK5))
    | ~ r1_xboole_0(sK2,sK3)
    | k1_relat_1(sK5) != sK3 ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_1521,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41818,c_4339,c_2871,c_2177,c_1887,c_1521,c_1512,c_1480,c_22,c_23,c_24,c_28,c_30,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.28/2.45  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.28/2.45  
% 15.28/2.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.28/2.45  
% 15.28/2.45  ------  iProver source info
% 15.28/2.45  
% 15.28/2.45  git: date: 2020-06-30 10:37:57 +0100
% 15.28/2.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.28/2.45  git: non_committed_changes: false
% 15.28/2.45  git: last_make_outside_of_git: false
% 15.28/2.45  
% 15.28/2.45  ------ 
% 15.28/2.45  ------ Parsing...
% 15.28/2.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.28/2.45  
% 15.28/2.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.28/2.45  
% 15.28/2.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.28/2.45  
% 15.28/2.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.28/2.45  ------ Proving...
% 15.28/2.45  ------ Problem Properties 
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  clauses                                 34
% 15.28/2.45  conjectures                             14
% 15.28/2.45  EPR                                     12
% 15.28/2.45  Horn                                    24
% 15.28/2.45  unary                                   14
% 15.28/2.45  binary                                  5
% 15.28/2.45  lits                                    141
% 15.28/2.45  lits eq                                 16
% 15.28/2.45  fd_pure                                 0
% 15.28/2.45  fd_pseudo                               0
% 15.28/2.45  fd_cond                                 0
% 15.28/2.45  fd_pseudo_cond                          1
% 15.28/2.45  AC symbols                              0
% 15.28/2.45  
% 15.28/2.45  ------ Input Options Time Limit: Unbounded
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  ------ 
% 15.28/2.45  Current options:
% 15.28/2.45  ------ 
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  ------ Proving...
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  % SZS status Theorem for theBenchmark.p
% 15.28/2.45  
% 15.28/2.45  % SZS output start CNFRefutation for theBenchmark.p
% 15.28/2.45  
% 15.28/2.45  fof(f15,conjecture,(
% 15.28/2.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f16,negated_conjecture,(
% 15.28/2.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 15.28/2.45    inference(negated_conjecture,[],[f15])).
% 15.28/2.45  
% 15.28/2.45  fof(f38,plain,(
% 15.28/2.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.28/2.45    inference(ennf_transformation,[],[f16])).
% 15.28/2.45  
% 15.28/2.45  fof(f39,plain,(
% 15.28/2.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 15.28/2.45    inference(flattening,[],[f38])).
% 15.28/2.45  
% 15.28/2.45  fof(f49,plain,(
% 15.28/2.45    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 15.28/2.45    introduced(choice_axiom,[])).
% 15.28/2.45  
% 15.28/2.45  fof(f48,plain,(
% 15.28/2.45    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 15.28/2.45    introduced(choice_axiom,[])).
% 15.28/2.45  
% 15.28/2.45  fof(f47,plain,(
% 15.28/2.45    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 15.28/2.45    introduced(choice_axiom,[])).
% 15.28/2.45  
% 15.28/2.45  fof(f46,plain,(
% 15.28/2.45    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 15.28/2.45    introduced(choice_axiom,[])).
% 15.28/2.45  
% 15.28/2.45  fof(f45,plain,(
% 15.28/2.45    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 15.28/2.45    introduced(choice_axiom,[])).
% 15.28/2.45  
% 15.28/2.45  fof(f44,plain,(
% 15.28/2.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 15.28/2.45    introduced(choice_axiom,[])).
% 15.28/2.45  
% 15.28/2.45  fof(f50,plain,(
% 15.28/2.45    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 15.28/2.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f49,f48,f47,f46,f45,f44])).
% 15.28/2.45  
% 15.28/2.45  fof(f78,plain,(
% 15.28/2.45    r1_subset_1(sK2,sK3)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f7,axiom,(
% 15.28/2.45    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f24,plain,(
% 15.28/2.45    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.28/2.45    inference(ennf_transformation,[],[f7])).
% 15.28/2.45  
% 15.28/2.45  fof(f25,plain,(
% 15.28/2.45    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.28/2.45    inference(flattening,[],[f24])).
% 15.28/2.45  
% 15.28/2.45  fof(f58,plain,(
% 15.28/2.45    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f25])).
% 15.28/2.45  
% 15.28/2.45  fof(f74,plain,(
% 15.28/2.45    ~v1_xboole_0(sK2)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f76,plain,(
% 15.28/2.45    ~v1_xboole_0(sK3)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f6,axiom,(
% 15.28/2.45    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f22,plain,(
% 15.28/2.45    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.28/2.45    inference(ennf_transformation,[],[f6])).
% 15.28/2.45  
% 15.28/2.45  fof(f23,plain,(
% 15.28/2.45    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.28/2.45    inference(flattening,[],[f22])).
% 15.28/2.45  
% 15.28/2.45  fof(f40,plain,(
% 15.28/2.45    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.28/2.45    inference(nnf_transformation,[],[f23])).
% 15.28/2.45  
% 15.28/2.45  fof(f56,plain,(
% 15.28/2.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f40])).
% 15.28/2.45  
% 15.28/2.45  fof(f81,plain,(
% 15.28/2.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f10,axiom,(
% 15.28/2.45    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f28,plain,(
% 15.28/2.45    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.28/2.45    inference(ennf_transformation,[],[f10])).
% 15.28/2.45  
% 15.28/2.45  fof(f29,plain,(
% 15.28/2.45    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 15.28/2.45    inference(flattening,[],[f28])).
% 15.28/2.45  
% 15.28/2.45  fof(f62,plain,(
% 15.28/2.45    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f29])).
% 15.28/2.45  
% 15.28/2.45  fof(f73,plain,(
% 15.28/2.45    ~v1_xboole_0(sK1)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f79,plain,(
% 15.28/2.45    v1_funct_1(sK4)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f80,plain,(
% 15.28/2.45    v1_funct_2(sK4,sK2,sK1)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f11,axiom,(
% 15.28/2.45    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f30,plain,(
% 15.28/2.45    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.28/2.45    inference(ennf_transformation,[],[f11])).
% 15.28/2.45  
% 15.28/2.45  fof(f31,plain,(
% 15.28/2.45    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.28/2.45    inference(flattening,[],[f30])).
% 15.28/2.45  
% 15.28/2.45  fof(f41,plain,(
% 15.28/2.45    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.28/2.45    inference(nnf_transformation,[],[f31])).
% 15.28/2.45  
% 15.28/2.45  fof(f63,plain,(
% 15.28/2.45    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f41])).
% 15.28/2.45  
% 15.28/2.45  fof(f8,axiom,(
% 15.28/2.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f26,plain,(
% 15.28/2.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.45    inference(ennf_transformation,[],[f8])).
% 15.28/2.45  
% 15.28/2.45  fof(f59,plain,(
% 15.28/2.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.28/2.45    inference(cnf_transformation,[],[f26])).
% 15.28/2.45  
% 15.28/2.45  fof(f9,axiom,(
% 15.28/2.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f17,plain,(
% 15.28/2.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.28/2.45    inference(pure_predicate_removal,[],[f9])).
% 15.28/2.45  
% 15.28/2.45  fof(f27,plain,(
% 15.28/2.45    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.45    inference(ennf_transformation,[],[f17])).
% 15.28/2.45  
% 15.28/2.45  fof(f60,plain,(
% 15.28/2.45    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.28/2.45    inference(cnf_transformation,[],[f27])).
% 15.28/2.45  
% 15.28/2.45  fof(f4,axiom,(
% 15.28/2.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f20,plain,(
% 15.28/2.45    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.28/2.45    inference(ennf_transformation,[],[f4])).
% 15.28/2.45  
% 15.28/2.45  fof(f54,plain,(
% 15.28/2.45    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f20])).
% 15.28/2.45  
% 15.28/2.45  fof(f5,axiom,(
% 15.28/2.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f21,plain,(
% 15.28/2.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.28/2.45    inference(ennf_transformation,[],[f5])).
% 15.28/2.45  
% 15.28/2.45  fof(f55,plain,(
% 15.28/2.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f21])).
% 15.28/2.45  
% 15.28/2.45  fof(f77,plain,(
% 15.28/2.45    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f2,axiom,(
% 15.28/2.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f18,plain,(
% 15.28/2.45    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 15.28/2.45    inference(ennf_transformation,[],[f2])).
% 15.28/2.45  
% 15.28/2.45  fof(f52,plain,(
% 15.28/2.45    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 15.28/2.45    inference(cnf_transformation,[],[f18])).
% 15.28/2.45  
% 15.28/2.45  fof(f12,axiom,(
% 15.28/2.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f32,plain,(
% 15.28/2.45    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.28/2.45    inference(ennf_transformation,[],[f12])).
% 15.28/2.45  
% 15.28/2.45  fof(f33,plain,(
% 15.28/2.45    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.28/2.45    inference(flattening,[],[f32])).
% 15.28/2.45  
% 15.28/2.45  fof(f65,plain,(
% 15.28/2.45    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f33])).
% 15.28/2.45  
% 15.28/2.45  fof(f84,plain,(
% 15.28/2.45    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f82,plain,(
% 15.28/2.45    v1_funct_1(sK5)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f13,axiom,(
% 15.28/2.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f34,plain,(
% 15.28/2.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.28/2.45    inference(ennf_transformation,[],[f13])).
% 15.28/2.45  
% 15.28/2.45  fof(f35,plain,(
% 15.28/2.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.28/2.45    inference(flattening,[],[f34])).
% 15.28/2.45  
% 15.28/2.45  fof(f42,plain,(
% 15.28/2.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.28/2.45    inference(nnf_transformation,[],[f35])).
% 15.28/2.45  
% 15.28/2.45  fof(f43,plain,(
% 15.28/2.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 15.28/2.45    inference(flattening,[],[f42])).
% 15.28/2.45  
% 15.28/2.45  fof(f66,plain,(
% 15.28/2.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f43])).
% 15.28/2.45  
% 15.28/2.45  fof(f90,plain,(
% 15.28/2.45    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(equality_resolution,[],[f66])).
% 15.28/2.45  
% 15.28/2.45  fof(f14,axiom,(
% 15.28/2.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f36,plain,(
% 15.28/2.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 15.28/2.45    inference(ennf_transformation,[],[f14])).
% 15.28/2.45  
% 15.28/2.45  fof(f37,plain,(
% 15.28/2.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 15.28/2.45    inference(flattening,[],[f36])).
% 15.28/2.45  
% 15.28/2.45  fof(f69,plain,(
% 15.28/2.45    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f37])).
% 15.28/2.45  
% 15.28/2.45  fof(f70,plain,(
% 15.28/2.45    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f37])).
% 15.28/2.45  
% 15.28/2.45  fof(f71,plain,(
% 15.28/2.45    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f37])).
% 15.28/2.45  
% 15.28/2.45  fof(f83,plain,(
% 15.28/2.45    v1_funct_2(sK5,sK3,sK1)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f72,plain,(
% 15.28/2.45    ~v1_xboole_0(sK0)),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f75,plain,(
% 15.28/2.45    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f85,plain,(
% 15.28/2.45    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 15.28/2.45    inference(cnf_transformation,[],[f50])).
% 15.28/2.45  
% 15.28/2.45  fof(f67,plain,(
% 15.28/2.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f43])).
% 15.28/2.45  
% 15.28/2.45  fof(f89,plain,(
% 15.28/2.45    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 15.28/2.45    inference(equality_resolution,[],[f67])).
% 15.28/2.45  
% 15.28/2.45  fof(f1,axiom,(
% 15.28/2.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.28/2.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.28/2.45  
% 15.28/2.45  fof(f51,plain,(
% 15.28/2.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.28/2.45    inference(cnf_transformation,[],[f1])).
% 15.28/2.45  
% 15.28/2.45  cnf(c_28,negated_conjecture,
% 15.28/2.45      ( r1_subset_1(sK2,sK3) ),
% 15.28/2.45      inference(cnf_transformation,[],[f78]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_461,negated_conjecture,
% 15.28/2.45      ( r1_subset_1(sK2,sK3) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_28]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1088,plain,
% 15.28/2.45      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_7,plain,
% 15.28/2.45      ( ~ r1_subset_1(X0,X1)
% 15.28/2.45      | r1_subset_1(X1,X0)
% 15.28/2.45      | v1_xboole_0(X0)
% 15.28/2.45      | v1_xboole_0(X1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f58]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_479,plain,
% 15.28/2.45      ( ~ r1_subset_1(X0_53,X1_53)
% 15.28/2.45      | r1_subset_1(X1_53,X0_53)
% 15.28/2.45      | v1_xboole_0(X1_53)
% 15.28/2.45      | v1_xboole_0(X0_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_7]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1071,plain,
% 15.28/2.45      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 15.28/2.45      | r1_subset_1(X1_53,X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X1_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_3797,plain,
% 15.28/2.45      ( r1_subset_1(sK3,sK2) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK3) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK2) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1088,c_1071]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_32,negated_conjecture,
% 15.28/2.45      ( ~ v1_xboole_0(sK2) ),
% 15.28/2.45      inference(cnf_transformation,[],[f74]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_37,plain,
% 15.28/2.45      ( v1_xboole_0(sK2) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_30,negated_conjecture,
% 15.28/2.45      ( ~ v1_xboole_0(sK3) ),
% 15.28/2.45      inference(cnf_transformation,[],[f76]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_39,plain,
% 15.28/2.45      ( v1_xboole_0(sK3) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_41,plain,
% 15.28/2.45      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1518,plain,
% 15.28/2.45      ( r1_subset_1(sK3,sK2)
% 15.28/2.45      | ~ r1_subset_1(sK2,sK3)
% 15.28/2.45      | v1_xboole_0(sK3)
% 15.28/2.45      | v1_xboole_0(sK2) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_479]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1519,plain,
% 15.28/2.45      ( r1_subset_1(sK3,sK2) = iProver_top
% 15.28/2.45      | r1_subset_1(sK2,sK3) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK3) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK2) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_4359,plain,
% 15.28/2.45      ( r1_subset_1(sK3,sK2) = iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_3797,c_37,c_39,c_41,c_1519]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_6,plain,
% 15.28/2.45      ( ~ r1_subset_1(X0,X1)
% 15.28/2.45      | r1_xboole_0(X0,X1)
% 15.28/2.45      | v1_xboole_0(X0)
% 15.28/2.45      | v1_xboole_0(X1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f56]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_480,plain,
% 15.28/2.45      ( ~ r1_subset_1(X0_53,X1_53)
% 15.28/2.45      | r1_xboole_0(X0_53,X1_53)
% 15.28/2.45      | v1_xboole_0(X1_53)
% 15.28/2.45      | v1_xboole_0(X0_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_6]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1070,plain,
% 15.28/2.45      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 15.28/2.45      | r1_xboole_0(X0_53,X1_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X1_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_4365,plain,
% 15.28/2.45      ( r1_xboole_0(sK3,sK2) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK3) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK2) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_4359,c_1070]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1745,plain,
% 15.28/2.45      ( ~ r1_subset_1(sK3,sK2)
% 15.28/2.45      | r1_xboole_0(sK3,sK2)
% 15.28/2.45      | v1_xboole_0(sK3)
% 15.28/2.45      | v1_xboole_0(sK2) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_480]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1747,plain,
% 15.28/2.45      ( r1_subset_1(sK3,sK2) != iProver_top
% 15.28/2.45      | r1_xboole_0(sK3,sK2) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK3) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK2) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_1745]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_4374,plain,
% 15.28/2.45      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_4365,c_37,c_39,c_41,c_1519,c_1747]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_25,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 15.28/2.45      inference(cnf_transformation,[],[f81]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_464,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_25]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1085,plain,
% 15.28/2.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_10,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | v1_partfun1(X0,X1)
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | v1_xboole_0(X2) ),
% 15.28/2.45      inference(cnf_transformation,[],[f62]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_476,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 15.28/2.45      | v1_partfun1(X0_53,X1_53)
% 15.28/2.45      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.28/2.45      | ~ v1_funct_1(X0_53)
% 15.28/2.45      | v1_xboole_0(X2_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_10]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1074,plain,
% 15.28/2.45      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 15.28/2.45      | v1_partfun1(X0_53,X1_53) = iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 15.28/2.45      | v1_funct_1(X0_53) != iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_5534,plain,
% 15.28/2.45      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 15.28/2.45      | v1_partfun1(sK4,sK2) = iProver_top
% 15.28/2.45      | v1_funct_1(sK4) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK1) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1085,c_1074]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_33,negated_conjecture,
% 15.28/2.45      ( ~ v1_xboole_0(sK1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f73]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_36,plain,
% 15.28/2.45      ( v1_xboole_0(sK1) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27,negated_conjecture,
% 15.28/2.45      ( v1_funct_1(sK4) ),
% 15.28/2.45      inference(cnf_transformation,[],[f79]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_42,plain,
% 15.28/2.45      ( v1_funct_1(sK4) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_26,negated_conjecture,
% 15.28/2.45      ( v1_funct_2(sK4,sK2,sK1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f80]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_43,plain,
% 15.28/2.45      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_44,plain,
% 15.28/2.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1618,plain,
% 15.28/2.45      ( ~ v1_funct_2(sK4,X0_53,X1_53)
% 15.28/2.45      | v1_partfun1(sK4,X0_53)
% 15.28/2.45      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 15.28/2.45      | ~ v1_funct_1(sK4)
% 15.28/2.45      | v1_xboole_0(X1_53) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_476]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1890,plain,
% 15.28/2.45      ( ~ v1_funct_2(sK4,sK2,sK1)
% 15.28/2.45      | v1_partfun1(sK4,sK2)
% 15.28/2.45      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.28/2.45      | ~ v1_funct_1(sK4)
% 15.28/2.45      | v1_xboole_0(sK1) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1618]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1891,plain,
% 15.28/2.45      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 15.28/2.45      | v1_partfun1(sK4,sK2) = iProver_top
% 15.28/2.45      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.28/2.45      | v1_funct_1(sK4) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK1) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_6050,plain,
% 15.28/2.45      ( v1_partfun1(sK4,sK2) = iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_5534,c_36,c_42,c_43,c_44,c_1891]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_13,plain,
% 15.28/2.45      ( ~ v1_partfun1(X0,X1)
% 15.28/2.45      | ~ v4_relat_1(X0,X1)
% 15.28/2.45      | ~ v1_relat_1(X0)
% 15.28/2.45      | k1_relat_1(X0) = X1 ),
% 15.28/2.45      inference(cnf_transformation,[],[f63]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_474,plain,
% 15.28/2.45      ( ~ v1_partfun1(X0_53,X1_53)
% 15.28/2.45      | ~ v4_relat_1(X0_53,X1_53)
% 15.28/2.45      | ~ v1_relat_1(X0_53)
% 15.28/2.45      | k1_relat_1(X0_53) = X1_53 ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_13]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1076,plain,
% 15.28/2.45      ( k1_relat_1(X0_53) = X1_53
% 15.28/2.45      | v1_partfun1(X0_53,X1_53) != iProver_top
% 15.28/2.45      | v4_relat_1(X0_53,X1_53) != iProver_top
% 15.28/2.45      | v1_relat_1(X0_53) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24483,plain,
% 15.28/2.45      ( k1_relat_1(sK4) = sK2
% 15.28/2.45      | v4_relat_1(sK4,sK2) != iProver_top
% 15.28/2.45      | v1_relat_1(sK4) != iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_6050,c_1076]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_8,plain,
% 15.28/2.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | v1_relat_1(X0) ),
% 15.28/2.45      inference(cnf_transformation,[],[f59]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_478,plain,
% 15.28/2.45      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.28/2.45      | v1_relat_1(X0_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_8]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1483,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.28/2.45      | v1_relat_1(sK4) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_478]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_9,plain,
% 15.28/2.45      ( v4_relat_1(X0,X1)
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.28/2.45      inference(cnf_transformation,[],[f60]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_477,plain,
% 15.28/2.45      ( v4_relat_1(X0_53,X1_53)
% 15.28/2.45      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_9]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1515,plain,
% 15.28/2.45      ( v4_relat_1(sK4,sK2)
% 15.28/2.45      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_477]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1722,plain,
% 15.28/2.45      ( ~ v1_partfun1(sK4,X0_53)
% 15.28/2.45      | ~ v4_relat_1(sK4,X0_53)
% 15.28/2.45      | ~ v1_relat_1(sK4)
% 15.28/2.45      | k1_relat_1(sK4) = X0_53 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_474]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1729,plain,
% 15.28/2.45      ( ~ v1_partfun1(sK4,sK2)
% 15.28/2.45      | ~ v4_relat_1(sK4,sK2)
% 15.28/2.45      | ~ v1_relat_1(sK4)
% 15.28/2.45      | k1_relat_1(sK4) = sK2 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1722]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24500,plain,
% 15.28/2.45      ( k1_relat_1(sK4) = sK2 ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_24483,c_33,c_27,c_26,c_25,c_1483,c_1515,c_1729,c_1890]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_3,plain,
% 15.28/2.45      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 15.28/2.45      | ~ v1_relat_1(X1)
% 15.28/2.45      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 15.28/2.45      inference(cnf_transformation,[],[f54]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_483,plain,
% 15.28/2.45      ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
% 15.28/2.45      | ~ v1_relat_1(X1_53)
% 15.28/2.45      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_3]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1067,plain,
% 15.28/2.45      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 15.28/2.45      | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
% 15.28/2.45      | v1_relat_1(X0_53) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24673,plain,
% 15.28/2.45      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 15.28/2.45      | r1_xboole_0(X0_53,sK2) != iProver_top
% 15.28/2.45      | v1_relat_1(sK4) != iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_24500,c_1067]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1484,plain,
% 15.28/2.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.28/2.45      | v1_relat_1(sK4) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_1483]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_41808,plain,
% 15.28/2.45      ( r1_xboole_0(X0_53,sK2) != iProver_top
% 15.28/2.45      | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_24673,c_44,c_1484]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_41809,plain,
% 15.28/2.45      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 15.28/2.45      | r1_xboole_0(X0_53,sK2) != iProver_top ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_41808]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_41816,plain,
% 15.28/2.45      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_4374,c_41809]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1072,plain,
% 15.28/2.45      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 15.28/2.45      | v1_relat_1(X0_53) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2212,plain,
% 15.28/2.45      ( v1_relat_1(sK4) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1085,c_1072]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_4,plain,
% 15.28/2.45      ( ~ v1_relat_1(X0)
% 15.28/2.45      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f55]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_482,plain,
% 15.28/2.45      ( ~ v1_relat_1(X0_53)
% 15.28/2.45      | k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_4]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1068,plain,
% 15.28/2.45      ( k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53)
% 15.28/2.45      | v1_relat_1(X0_53) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2396,plain,
% 15.28/2.45      ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_53)) = k7_relat_1(sK4,X0_53) ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_2212,c_1068]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24549,plain,
% 15.28/2.45      ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_53)) = k7_relat_1(sK4,X0_53) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_24500,c_2396]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_29,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 15.28/2.45      inference(cnf_transformation,[],[f77]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_460,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_29]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1089,plain,
% 15.28/2.45      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_460]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1,plain,
% 15.28/2.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.28/2.45      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 15.28/2.45      inference(cnf_transformation,[],[f52]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_485,plain,
% 15.28/2.45      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 15.28/2.45      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_1]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1065,plain,
% 15.28/2.45      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 15.28/2.45      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1843,plain,
% 15.28/2.45      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1089,c_1065]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_14,plain,
% 15.28/2.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.28/2.45      inference(cnf_transformation,[],[f65]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_473,plain,
% 15.28/2.45      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.28/2.45      | ~ v1_funct_1(X0_53)
% 15.28/2.45      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_14]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1077,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 15.28/2.45      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 15.28/2.45      | v1_funct_1(X2_53) != iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_6730,plain,
% 15.28/2.45      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 15.28/2.45      | v1_funct_1(sK4) != iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1085,c_1077]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1592,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 15.28/2.45      | ~ v1_funct_1(sK4)
% 15.28/2.45      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_473]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1882,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.28/2.45      | ~ v1_funct_1(sK4)
% 15.28/2.45      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1592]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_7299,plain,
% 15.28/2.45      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_6730,c_27,c_25,c_1882]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_22,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 15.28/2.45      inference(cnf_transformation,[],[f84]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_467,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_22]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1082,plain,
% 15.28/2.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_6729,plain,
% 15.28/2.45      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 15.28/2.45      | v1_funct_1(sK5) != iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1082,c_1077]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24,negated_conjecture,
% 15.28/2.45      ( v1_funct_1(sK5) ),
% 15.28/2.45      inference(cnf_transformation,[],[f82]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1587,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 15.28/2.45      | ~ v1_funct_1(sK5)
% 15.28/2.45      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_473]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1877,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 15.28/2.45      | ~ v1_funct_1(sK5)
% 15.28/2.45      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1587]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_7293,plain,
% 15.28/2.45      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_6729,c_24,c_22,c_1877]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_17,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 15.28/2.45      inference(cnf_transformation,[],[f90]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f69]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_19,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f70]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_18,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f71]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_274,plain,
% 15.28/2.45      ( ~ v1_funct_1(X3)
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_17,c_20,c_19,c_18]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_275,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | v1_xboole_0(X1)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_274]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_453,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 15.28/2.45      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 15.28/2.45      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 15.28/2.45      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 15.28/2.45      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.28/2.45      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 15.28/2.45      | ~ v1_funct_1(X0_53)
% 15.28/2.45      | ~ v1_funct_1(X3_53)
% 15.28/2.45      | v1_xboole_0(X1_53)
% 15.28/2.45      | v1_xboole_0(X2_53)
% 15.28/2.45      | v1_xboole_0(X4_53)
% 15.28/2.45      | v1_xboole_0(X5_53)
% 15.28/2.45      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_275]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1096,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 15.28/2.45      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 15.28/2.45      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 15.28/2.45      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 15.28/2.45      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 15.28/2.45      | v1_funct_1(X2_53) != iProver_top
% 15.28/2.45      | v1_funct_1(X5_53) != iProver_top
% 15.28/2.45      | v1_xboole_0(X3_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X1_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X4_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_21402,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 15.28/2.45      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 15.28/2.45      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | v1_funct_1(X1_53) != iProver_top
% 15.28/2.45      | v1_funct_1(sK5) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK1) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK3) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_7293,c_1096]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_45,plain,
% 15.28/2.45      ( v1_funct_1(sK5) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_23,negated_conjecture,
% 15.28/2.45      ( v1_funct_2(sK5,sK3,sK1) ),
% 15.28/2.45      inference(cnf_transformation,[],[f83]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_46,plain,
% 15.28/2.45      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_47,plain,
% 15.28/2.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27275,plain,
% 15.28/2.45      ( v1_funct_1(X1_53) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 15.28/2.45      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 15.28/2.45      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_21402,c_36,c_39,c_45,c_46,c_47]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27276,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 15.28/2.45      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | v1_funct_1(X1_53) != iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_27275]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27291,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 15.28/2.45      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 15.28/2.45      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 15.28/2.45      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | v1_funct_1(sK4) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK2) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_7299,c_27276]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27337,plain,
% 15.28/2.45      ( v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 15.28/2.45      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_27291,c_37,c_42,c_43,c_44]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27338,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 15.28/2.45      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_27337]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27348,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 15.28/2.45      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK0) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1843,c_27338]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27349,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 15.28/2.45      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK0) = iProver_top ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_27348,c_1843]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_34,negated_conjecture,
% 15.28/2.45      ( ~ v1_xboole_0(sK0) ),
% 15.28/2.45      inference(cnf_transformation,[],[f72]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_31,negated_conjecture,
% 15.28/2.45      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 15.28/2.45      inference(cnf_transformation,[],[f75]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_21,negated_conjecture,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 15.28/2.45      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 15.28/2.45      inference(cnf_transformation,[],[f85]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_468,negated_conjecture,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 15.28/2.45      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_21]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2036,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 15.28/2.45      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_1843,c_468]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_7297,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 15.28/2.45      | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_7293,c_2036]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_7385,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 15.28/2.45      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_7297,c_7299]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_16,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 15.28/2.45      inference(cnf_transformation,[],[f89]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_265,plain,
% 15.28/2.45      ( ~ v1_funct_1(X3)
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X1)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_16,c_20,c_19,c_18]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_266,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.45      | ~ v1_funct_2(X3,X4,X2)
% 15.28/2.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 15.28/2.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 15.28/2.45      | ~ v1_funct_1(X0)
% 15.28/2.45      | ~ v1_funct_1(X3)
% 15.28/2.45      | v1_xboole_0(X1)
% 15.28/2.45      | v1_xboole_0(X2)
% 15.28/2.45      | v1_xboole_0(X4)
% 15.28/2.45      | v1_xboole_0(X5)
% 15.28/2.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_265]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_454,plain,
% 15.28/2.45      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 15.28/2.45      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 15.28/2.45      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 15.28/2.45      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 15.28/2.45      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 15.28/2.45      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 15.28/2.45      | ~ v1_funct_1(X0_53)
% 15.28/2.45      | ~ v1_funct_1(X3_53)
% 15.28/2.45      | v1_xboole_0(X1_53)
% 15.28/2.45      | v1_xboole_0(X2_53)
% 15.28/2.45      | v1_xboole_0(X4_53)
% 15.28/2.45      | v1_xboole_0(X5_53)
% 15.28/2.45      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_266]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1095,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 15.28/2.45      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 15.28/2.45      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 15.28/2.45      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 15.28/2.45      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 15.28/2.45      | v1_funct_1(X2_53) != iProver_top
% 15.28/2.45      | v1_funct_1(X5_53) != iProver_top
% 15.28/2.45      | v1_xboole_0(X3_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X1_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X4_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_19103,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 15.28/2.45      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 15.28/2.45      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | v1_funct_1(X1_53) != iProver_top
% 15.28/2.45      | v1_funct_1(sK5) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK1) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK3) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_7293,c_1095]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20519,plain,
% 15.28/2.45      ( v1_funct_1(X1_53) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 15.28/2.45      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 15.28/2.45      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_19103,c_36,c_39,c_45,c_46,c_47]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20520,plain,
% 15.28/2.45      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 15.28/2.45      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 15.28/2.45      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 15.28/2.45      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 15.28/2.45      | v1_funct_1(X1_53) != iProver_top
% 15.28/2.45      | v1_xboole_0(X2_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_20519]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20535,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 15.28/2.45      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 15.28/2.45      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | v1_funct_1(sK4) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | v1_xboole_0(sK2) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_7299,c_20520]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20859,plain,
% 15.28/2.45      ( v1_xboole_0(X0_53) = iProver_top
% 15.28/2.45      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_20535,c_37,c_42,c_43,c_44]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20860,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 15.28/2.45      | v1_xboole_0(X0_53) = iProver_top ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_20859]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20870,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK0) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1843,c_20860]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20871,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 15.28/2.45      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK0) = iProver_top ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_20870,c_1843]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20872,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 15.28/2.45      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 15.28/2.45      | v1_xboole_0(sK0)
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(predicate_to_equality_rev,[status(thm)],[c_20871]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20874,plain,
% 15.28/2.45      ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_20871,c_34,c_31,c_29,c_20872]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_20875,plain,
% 15.28/2.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 15.28/2.45      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(renaming,[status(thm)],[c_20874]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27350,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 15.28/2.45      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 15.28/2.45      | v1_xboole_0(sK0)
% 15.28/2.45      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 15.28/2.45      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(predicate_to_equality_rev,[status(thm)],[c_27349]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_27553,plain,
% 15.28/2.45      ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_27349,c_34,c_31,c_29,c_7385,c_20875,c_27350]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_33063,plain,
% 15.28/2.45      ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,sK3) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_24549,c_27553]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_5533,plain,
% 15.28/2.45      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 15.28/2.45      | v1_partfun1(sK5,sK3) = iProver_top
% 15.28/2.45      | v1_funct_1(sK5) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK1) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1082,c_1074]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1613,plain,
% 15.28/2.45      ( ~ v1_funct_2(sK5,X0_53,X1_53)
% 15.28/2.45      | v1_partfun1(sK5,X0_53)
% 15.28/2.45      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 15.28/2.45      | ~ v1_funct_1(sK5)
% 15.28/2.45      | v1_xboole_0(X1_53) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_476]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1887,plain,
% 15.28/2.45      ( ~ v1_funct_2(sK5,sK3,sK1)
% 15.28/2.45      | v1_partfun1(sK5,sK3)
% 15.28/2.45      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 15.28/2.45      | ~ v1_funct_1(sK5)
% 15.28/2.45      | v1_xboole_0(sK1) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1613]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1888,plain,
% 15.28/2.45      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 15.28/2.45      | v1_partfun1(sK5,sK3) = iProver_top
% 15.28/2.45      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 15.28/2.45      | v1_funct_1(sK5) != iProver_top
% 15.28/2.45      | v1_xboole_0(sK1) = iProver_top ),
% 15.28/2.45      inference(predicate_to_equality,[status(thm)],[c_1887]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_5978,plain,
% 15.28/2.45      ( v1_partfun1(sK5,sK3) = iProver_top ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_5533,c_36,c_45,c_46,c_47,c_1888]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24484,plain,
% 15.28/2.45      ( k1_relat_1(sK5) = sK3
% 15.28/2.45      | v4_relat_1(sK5,sK3) != iProver_top
% 15.28/2.45      | v1_relat_1(sK5) != iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_5978,c_1076]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1480,plain,
% 15.28/2.45      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 15.28/2.45      | v1_relat_1(sK5) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_478]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1512,plain,
% 15.28/2.45      ( v4_relat_1(sK5,sK3)
% 15.28/2.45      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_477]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1707,plain,
% 15.28/2.45      ( ~ v1_partfun1(sK5,X0_53)
% 15.28/2.45      | ~ v4_relat_1(sK5,X0_53)
% 15.28/2.45      | ~ v1_relat_1(sK5)
% 15.28/2.45      | k1_relat_1(sK5) = X0_53 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_474]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2177,plain,
% 15.28/2.45      ( ~ v1_partfun1(sK5,sK3)
% 15.28/2.45      | ~ v4_relat_1(sK5,sK3)
% 15.28/2.45      | ~ v1_relat_1(sK5)
% 15.28/2.45      | k1_relat_1(sK5) = sK3 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1707]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24788,plain,
% 15.28/2.45      ( k1_relat_1(sK5) = sK3 ),
% 15.28/2.45      inference(global_propositional_subsumption,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_24484,c_33,c_24,c_23,c_22,c_1480,c_1512,c_1887,c_2177]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_0,plain,
% 15.28/2.45      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.28/2.45      inference(cnf_transformation,[],[f51]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_486,plain,
% 15.28/2.45      ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
% 15.28/2.45      inference(subtyping,[status(esa)],[c_0]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2211,plain,
% 15.28/2.45      ( v1_relat_1(sK5) = iProver_top ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_1082,c_1072]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2386,plain,
% 15.28/2.45      ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_53)) = k7_relat_1(sK5,X0_53) ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_2211,c_1068]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2683,plain,
% 15.28/2.45      ( k7_relat_1(sK5,k3_xboole_0(X0_53,k1_relat_1(sK5))) = k7_relat_1(sK5,X0_53) ),
% 15.28/2.45      inference(superposition,[status(thm)],[c_486,c_2386]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_24838,plain,
% 15.28/2.45      ( k7_relat_1(sK5,k3_xboole_0(X0_53,sK3)) = k7_relat_1(sK5,X0_53) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_24788,c_2683]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_33752,plain,
% 15.28/2.45      ( k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_33063,c_24838]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_41818,plain,
% 15.28/2.45      ( k7_relat_1(sK5,sK2) != k1_xboole_0 ),
% 15.28/2.45      inference(demodulation,[status(thm)],[c_41816,c_33752]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_4339,plain,
% 15.28/2.45      ( ~ r1_xboole_0(sK2,k1_relat_1(sK5))
% 15.28/2.45      | ~ v1_relat_1(sK5)
% 15.28/2.45      | k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_483]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_496,plain,
% 15.28/2.45      ( ~ r1_xboole_0(X0_53,X1_53)
% 15.28/2.45      | r1_xboole_0(X0_53,X2_53)
% 15.28/2.45      | X2_53 != X1_53 ),
% 15.28/2.45      theory(equality) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1754,plain,
% 15.28/2.45      ( r1_xboole_0(sK2,X0_53) | ~ r1_xboole_0(sK2,sK3) | X0_53 != sK3 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_496]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_2871,plain,
% 15.28/2.45      ( r1_xboole_0(sK2,k1_relat_1(sK5))
% 15.28/2.45      | ~ r1_xboole_0(sK2,sK3)
% 15.28/2.45      | k1_relat_1(sK5) != sK3 ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_1754]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(c_1521,plain,
% 15.28/2.45      ( ~ r1_subset_1(sK2,sK3)
% 15.28/2.45      | r1_xboole_0(sK2,sK3)
% 15.28/2.45      | v1_xboole_0(sK3)
% 15.28/2.45      | v1_xboole_0(sK2) ),
% 15.28/2.45      inference(instantiation,[status(thm)],[c_480]) ).
% 15.28/2.45  
% 15.28/2.45  cnf(contradiction,plain,
% 15.28/2.45      ( $false ),
% 15.28/2.45      inference(minisat,
% 15.28/2.45                [status(thm)],
% 15.28/2.45                [c_41818,c_4339,c_2871,c_2177,c_1887,c_1521,c_1512,
% 15.28/2.45                 c_1480,c_22,c_23,c_24,c_28,c_30,c_32,c_33]) ).
% 15.28/2.45  
% 15.28/2.45  
% 15.28/2.45  % SZS output end CNFRefutation for theBenchmark.p
% 15.28/2.45  
% 15.28/2.45  ------                               Statistics
% 15.28/2.45  
% 15.28/2.45  ------ Selected
% 15.28/2.45  
% 15.28/2.45  total_time:                             1.504
% 15.28/2.45  
%------------------------------------------------------------------------------
