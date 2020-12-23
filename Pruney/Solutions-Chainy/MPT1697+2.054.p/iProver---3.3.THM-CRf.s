%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:34 EST 2020

% Result     : Theorem 7.70s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  204 (3341 expanded)
%              Number of clauses        :  137 ( 790 expanded)
%              Number of leaves         :   17 (1372 expanded)
%              Depth                    :   27
%              Number of atoms          : 1193 (46474 expanded)
%              Number of equality atoms :  499 (11102 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f34])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f46,f45,f44,f43,f42,f41])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f64])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f32])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
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
    inference(equality_resolution,[],[f63])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_855,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1309,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1303,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_2090,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1303])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_452,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_453,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_841,plain,
    ( k3_xboole_0(k1_xboole_0,X0_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_257,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_536,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X2,X3) != k1_xboole_0
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_257,c_5])).

cnf(c_537,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_840,plain,
    ( ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | k3_xboole_0(X1_54,k1_relat_1(X0_54)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_537])).

cnf(c_1323,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | k3_xboole_0(X1_54,k1_relat_1(X0_54)) != k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_18550,plain,
    ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_1323])).

cnf(c_18619,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2090,c_18550])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_849,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1315,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1302,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_2137,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
    inference(superposition,[status(thm)],[c_1315,c_1302])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_852,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1312,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_861,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1304,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_2215,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1304])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1702,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1860,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_1702])).

cnf(c_2849,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2215,c_27,c_25,c_1860])).

cnf(c_2214,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1304])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1697,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1855,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(instantiation,[status(thm)],[c_1697])).

cnf(c_2810,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2214,c_24,c_22,c_1855])).

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
    inference(cnf_transformation,[],[f86])).

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
    inference(cnf_transformation,[],[f66])).

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
    inference(cnf_transformation,[],[f67])).

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
    inference(cnf_transformation,[],[f68])).

cnf(c_199,plain,
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

cnf(c_200,plain,
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
    inference(renaming,[status(thm)],[c_199])).

cnf(c_842,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_200])).

cnf(c_1322,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_5413,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2810,c_1322])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16466,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5413,c_36,c_39,c_45,c_46,c_47])).

cnf(c_16467,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_16466])).

cnf(c_16482,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_16467])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16616,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16482,c_37,c_42,c_43,c_44])).

cnf(c_16617,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_16616])).

cnf(c_16627,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_16617])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_259,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_522,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_523,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_525,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_523,c_32,c_30])).

cnf(c_551,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_525])).

cnf(c_552,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_839,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_552])).

cnf(c_16628,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16627,c_839])).

cnf(c_859,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1306,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_2334,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1306,c_1304])).

cnf(c_857,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1308,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_6043,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2334,c_1308])).

cnf(c_6047,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_6043])).

cnf(c_6154,plain,
    ( v1_funct_1(X2_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6047,c_36,c_39,c_45,c_46])).

cnf(c_6155,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6154])).

cnf(c_6169,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_6155])).

cnf(c_6519,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6169,c_37,c_42,c_43])).

cnf(c_6520,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6519])).

cnf(c_6529,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_6520])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6534,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6529,c_35,c_38])).

cnf(c_16629,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16628,c_2137,c_6534])).

cnf(c_16630,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16629,c_839])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_856,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2208,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2137,c_856])).

cnf(c_2209,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2208,c_839])).

cnf(c_2853,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2209,c_2810,c_2849])).

cnf(c_6538,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6534,c_2853])).

cnf(c_6539,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6538,c_6534])).

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
    inference(cnf_transformation,[],[f87])).

cnf(c_192,plain,
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

cnf(c_193,plain,
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
    inference(renaming,[status(thm)],[c_192])).

cnf(c_843,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_193])).

cnf(c_1321,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_3092,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2810,c_1321])).

cnf(c_9711,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3092,c_36,c_39,c_45,c_46,c_47])).

cnf(c_9712,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_9711])).

cnf(c_9727,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2849,c_9712])).

cnf(c_10372,plain,
    ( v1_xboole_0(X0_54) = iProver_top
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9727,c_37,c_42,c_43,c_44])).

cnf(c_10373,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_10372])).

cnf(c_10383,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_10373])).

cnf(c_10384,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10383,c_839])).

cnf(c_10385,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10384,c_2137,c_6534])).

cnf(c_10386,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10385,c_839])).

cnf(c_10387,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10386])).

cnf(c_10389,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10386,c_34,c_31,c_29,c_10387])).

cnf(c_10390,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_10389])).

cnf(c_16631,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16630])).

cnf(c_16702,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16630,c_34,c_31,c_29,c_6539,c_10390,c_16631])).

cnf(c_18684,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18619,c_16702])).

cnf(c_2045,plain,
    ( k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_841])).

cnf(c_1789,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0_54) = k1_xboole_0
    | k3_xboole_0(X0_54,k1_relat_1(sK4)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_840])).

cnf(c_2044,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0
    | k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1789])).

cnf(c_1624,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18684,c_2045,c_2044,c_1624,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n018.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:01:57 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 7.70/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/1.47  
% 7.70/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.70/1.47  
% 7.70/1.47  ------  iProver source info
% 7.70/1.47  
% 7.70/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.70/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.70/1.47  git: non_committed_changes: false
% 7.70/1.47  git: last_make_outside_of_git: false
% 7.70/1.47  
% 7.70/1.47  ------ 
% 7.70/1.47  
% 7.70/1.47  ------ Input Options
% 7.70/1.47  
% 7.70/1.47  --out_options                           all
% 7.70/1.47  --tptp_safe_out                         true
% 7.70/1.47  --problem_path                          ""
% 7.70/1.47  --include_path                          ""
% 7.70/1.47  --clausifier                            res/vclausify_rel
% 7.70/1.47  --clausifier_options                    --mode clausify
% 7.70/1.47  --stdin                                 false
% 7.70/1.47  --stats_out                             all
% 7.70/1.47  
% 7.70/1.47  ------ General Options
% 7.70/1.47  
% 7.70/1.47  --fof                                   false
% 7.70/1.47  --time_out_real                         305.
% 7.70/1.47  --time_out_virtual                      -1.
% 7.70/1.47  --symbol_type_check                     false
% 7.70/1.47  --clausify_out                          false
% 7.70/1.47  --sig_cnt_out                           false
% 7.70/1.47  --trig_cnt_out                          false
% 7.70/1.47  --trig_cnt_out_tolerance                1.
% 7.70/1.47  --trig_cnt_out_sk_spl                   false
% 7.70/1.47  --abstr_cl_out                          false
% 7.70/1.47  
% 7.70/1.47  ------ Global Options
% 7.70/1.47  
% 7.70/1.47  --schedule                              default
% 7.70/1.47  --add_important_lit                     false
% 7.70/1.47  --prop_solver_per_cl                    1000
% 7.70/1.47  --min_unsat_core                        false
% 7.70/1.47  --soft_assumptions                      false
% 7.70/1.47  --soft_lemma_size                       3
% 7.70/1.47  --prop_impl_unit_size                   0
% 7.70/1.47  --prop_impl_unit                        []
% 7.70/1.47  --share_sel_clauses                     true
% 7.70/1.47  --reset_solvers                         false
% 7.70/1.47  --bc_imp_inh                            [conj_cone]
% 7.70/1.47  --conj_cone_tolerance                   3.
% 7.70/1.47  --extra_neg_conj                        none
% 7.70/1.47  --large_theory_mode                     true
% 7.70/1.47  --prolific_symb_bound                   200
% 7.70/1.47  --lt_threshold                          2000
% 7.70/1.47  --clause_weak_htbl                      true
% 7.70/1.47  --gc_record_bc_elim                     false
% 7.70/1.47  
% 7.70/1.47  ------ Preprocessing Options
% 7.70/1.47  
% 7.70/1.47  --preprocessing_flag                    true
% 7.70/1.47  --time_out_prep_mult                    0.1
% 7.70/1.47  --splitting_mode                        input
% 7.70/1.47  --splitting_grd                         true
% 7.70/1.47  --splitting_cvd                         false
% 7.70/1.47  --splitting_cvd_svl                     false
% 7.70/1.47  --splitting_nvd                         32
% 7.70/1.47  --sub_typing                            true
% 7.70/1.47  --prep_gs_sim                           true
% 7.70/1.47  --prep_unflatten                        true
% 7.70/1.47  --prep_res_sim                          true
% 7.70/1.47  --prep_upred                            true
% 7.70/1.47  --prep_sem_filter                       exhaustive
% 7.70/1.47  --prep_sem_filter_out                   false
% 7.70/1.47  --pred_elim                             true
% 7.70/1.47  --res_sim_input                         true
% 7.70/1.47  --eq_ax_congr_red                       true
% 7.70/1.47  --pure_diseq_elim                       true
% 7.70/1.47  --brand_transform                       false
% 7.70/1.47  --non_eq_to_eq                          false
% 7.70/1.47  --prep_def_merge                        true
% 7.70/1.47  --prep_def_merge_prop_impl              false
% 7.70/1.47  --prep_def_merge_mbd                    true
% 7.70/1.47  --prep_def_merge_tr_red                 false
% 7.70/1.47  --prep_def_merge_tr_cl                  false
% 7.70/1.47  --smt_preprocessing                     true
% 7.70/1.47  --smt_ac_axioms                         fast
% 7.70/1.47  --preprocessed_out                      false
% 7.70/1.47  --preprocessed_stats                    false
% 7.70/1.47  
% 7.70/1.47  ------ Abstraction refinement Options
% 7.70/1.47  
% 7.70/1.47  --abstr_ref                             []
% 7.70/1.47  --abstr_ref_prep                        false
% 7.70/1.47  --abstr_ref_until_sat                   false
% 7.70/1.47  --abstr_ref_sig_restrict                funpre
% 7.70/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.70/1.47  --abstr_ref_under                       []
% 7.70/1.47  
% 7.70/1.47  ------ SAT Options
% 7.70/1.47  
% 7.70/1.47  --sat_mode                              false
% 7.70/1.47  --sat_fm_restart_options                ""
% 7.70/1.47  --sat_gr_def                            false
% 7.70/1.47  --sat_epr_types                         true
% 7.70/1.47  --sat_non_cyclic_types                  false
% 7.70/1.47  --sat_finite_models                     false
% 7.70/1.47  --sat_fm_lemmas                         false
% 7.70/1.47  --sat_fm_prep                           false
% 7.70/1.47  --sat_fm_uc_incr                        true
% 7.70/1.47  --sat_out_model                         small
% 7.70/1.47  --sat_out_clauses                       false
% 7.70/1.47  
% 7.70/1.47  ------ QBF Options
% 7.70/1.47  
% 7.70/1.47  --qbf_mode                              false
% 7.70/1.47  --qbf_elim_univ                         false
% 7.70/1.47  --qbf_dom_inst                          none
% 7.70/1.47  --qbf_dom_pre_inst                      false
% 7.70/1.47  --qbf_sk_in                             false
% 7.70/1.47  --qbf_pred_elim                         true
% 7.70/1.47  --qbf_split                             512
% 7.70/1.47  
% 7.70/1.47  ------ BMC1 Options
% 7.70/1.47  
% 7.70/1.47  --bmc1_incremental                      false
% 7.70/1.47  --bmc1_axioms                           reachable_all
% 7.70/1.47  --bmc1_min_bound                        0
% 7.70/1.47  --bmc1_max_bound                        -1
% 7.70/1.47  --bmc1_max_bound_default                -1
% 7.70/1.47  --bmc1_symbol_reachability              true
% 7.70/1.47  --bmc1_property_lemmas                  false
% 7.70/1.47  --bmc1_k_induction                      false
% 7.70/1.47  --bmc1_non_equiv_states                 false
% 7.70/1.47  --bmc1_deadlock                         false
% 7.70/1.47  --bmc1_ucm                              false
% 7.70/1.47  --bmc1_add_unsat_core                   none
% 7.70/1.47  --bmc1_unsat_core_children              false
% 7.70/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.70/1.47  --bmc1_out_stat                         full
% 7.70/1.47  --bmc1_ground_init                      false
% 7.70/1.47  --bmc1_pre_inst_next_state              false
% 7.70/1.47  --bmc1_pre_inst_state                   false
% 7.70/1.47  --bmc1_pre_inst_reach_state             false
% 7.70/1.47  --bmc1_out_unsat_core                   false
% 7.70/1.47  --bmc1_aig_witness_out                  false
% 7.70/1.47  --bmc1_verbose                          false
% 7.70/1.47  --bmc1_dump_clauses_tptp                false
% 7.70/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.70/1.47  --bmc1_dump_file                        -
% 7.70/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.70/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.70/1.47  --bmc1_ucm_extend_mode                  1
% 7.70/1.47  --bmc1_ucm_init_mode                    2
% 7.70/1.47  --bmc1_ucm_cone_mode                    none
% 7.70/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.70/1.47  --bmc1_ucm_relax_model                  4
% 7.70/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.70/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.70/1.47  --bmc1_ucm_layered_model                none
% 7.70/1.47  --bmc1_ucm_max_lemma_size               10
% 7.70/1.47  
% 7.70/1.47  ------ AIG Options
% 7.70/1.47  
% 7.70/1.47  --aig_mode                              false
% 7.70/1.47  
% 7.70/1.47  ------ Instantiation Options
% 7.70/1.47  
% 7.70/1.47  --instantiation_flag                    true
% 7.70/1.47  --inst_sos_flag                         false
% 7.70/1.47  --inst_sos_phase                        true
% 7.70/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.70/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.70/1.47  --inst_lit_sel_side                     num_symb
% 7.70/1.47  --inst_solver_per_active                1400
% 7.70/1.47  --inst_solver_calls_frac                1.
% 7.70/1.47  --inst_passive_queue_type               priority_queues
% 7.70/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.70/1.47  --inst_passive_queues_freq              [25;2]
% 7.70/1.47  --inst_dismatching                      true
% 7.70/1.47  --inst_eager_unprocessed_to_passive     true
% 7.70/1.47  --inst_prop_sim_given                   true
% 7.70/1.47  --inst_prop_sim_new                     false
% 7.70/1.47  --inst_subs_new                         false
% 7.70/1.47  --inst_eq_res_simp                      false
% 7.70/1.47  --inst_subs_given                       false
% 7.70/1.47  --inst_orphan_elimination               true
% 7.70/1.47  --inst_learning_loop_flag               true
% 7.70/1.47  --inst_learning_start                   3000
% 7.70/1.47  --inst_learning_factor                  2
% 7.70/1.47  --inst_start_prop_sim_after_learn       3
% 7.70/1.47  --inst_sel_renew                        solver
% 7.70/1.47  --inst_lit_activity_flag                true
% 7.70/1.47  --inst_restr_to_given                   false
% 7.70/1.47  --inst_activity_threshold               500
% 7.70/1.47  --inst_out_proof                        true
% 7.70/1.47  
% 7.70/1.47  ------ Resolution Options
% 7.70/1.47  
% 7.70/1.47  --resolution_flag                       true
% 7.70/1.47  --res_lit_sel                           adaptive
% 7.70/1.47  --res_lit_sel_side                      none
% 7.70/1.47  --res_ordering                          kbo
% 7.70/1.47  --res_to_prop_solver                    active
% 7.70/1.47  --res_prop_simpl_new                    false
% 7.70/1.47  --res_prop_simpl_given                  true
% 7.70/1.47  --res_passive_queue_type                priority_queues
% 7.70/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.70/1.47  --res_passive_queues_freq               [15;5]
% 7.70/1.47  --res_forward_subs                      full
% 7.70/1.47  --res_backward_subs                     full
% 7.70/1.47  --res_forward_subs_resolution           true
% 7.70/1.47  --res_backward_subs_resolution          true
% 7.70/1.47  --res_orphan_elimination                true
% 7.70/1.47  --res_time_limit                        2.
% 7.70/1.47  --res_out_proof                         true
% 7.70/1.47  
% 7.70/1.47  ------ Superposition Options
% 7.70/1.47  
% 7.70/1.47  --superposition_flag                    true
% 7.70/1.47  --sup_passive_queue_type                priority_queues
% 7.70/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.70/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.70/1.47  --demod_completeness_check              fast
% 7.70/1.47  --demod_use_ground                      true
% 7.70/1.47  --sup_to_prop_solver                    passive
% 7.70/1.47  --sup_prop_simpl_new                    true
% 7.70/1.47  --sup_prop_simpl_given                  true
% 7.70/1.47  --sup_fun_splitting                     false
% 7.70/1.47  --sup_smt_interval                      50000
% 7.70/1.47  
% 7.70/1.47  ------ Superposition Simplification Setup
% 7.70/1.47  
% 7.70/1.47  --sup_indices_passive                   []
% 7.70/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.70/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.47  --sup_full_bw                           [BwDemod]
% 7.70/1.47  --sup_immed_triv                        [TrivRules]
% 7.70/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.70/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.47  --sup_immed_bw_main                     []
% 7.70/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.70/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.47  
% 7.70/1.47  ------ Combination Options
% 7.70/1.47  
% 7.70/1.47  --comb_res_mult                         3
% 7.70/1.47  --comb_sup_mult                         2
% 7.70/1.47  --comb_inst_mult                        10
% 7.70/1.47  
% 7.70/1.47  ------ Debug Options
% 7.70/1.47  
% 7.70/1.47  --dbg_backtrace                         false
% 7.70/1.47  --dbg_dump_prop_clauses                 false
% 7.70/1.47  --dbg_dump_prop_clauses_file            -
% 7.70/1.47  --dbg_out_stat                          false
% 7.70/1.47  ------ Parsing...
% 7.70/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.70/1.47  
% 7.70/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 7.70/1.47  
% 7.70/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.70/1.47  
% 7.70/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.70/1.47  ------ Proving...
% 7.70/1.47  ------ Problem Properties 
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  clauses                                 27
% 7.70/1.47  conjectures                             13
% 7.70/1.47  EPR                                     8
% 7.70/1.47  Horn                                    20
% 7.70/1.47  unary                                   14
% 7.70/1.47  binary                                  2
% 7.70/1.47  lits                                    119
% 7.70/1.47  lits eq                                 18
% 7.70/1.47  fd_pure                                 0
% 7.70/1.47  fd_pseudo                               0
% 7.70/1.47  fd_cond                                 0
% 7.70/1.47  fd_pseudo_cond                          1
% 7.70/1.47  AC symbols                              0
% 7.70/1.47  
% 7.70/1.47  ------ Schedule dynamic 5 is on 
% 7.70/1.47  
% 7.70/1.47  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  ------ 
% 7.70/1.47  Current options:
% 7.70/1.47  ------ 
% 7.70/1.47  
% 7.70/1.47  ------ Input Options
% 7.70/1.47  
% 7.70/1.47  --out_options                           all
% 7.70/1.47  --tptp_safe_out                         true
% 7.70/1.47  --problem_path                          ""
% 7.70/1.47  --include_path                          ""
% 7.70/1.47  --clausifier                            res/vclausify_rel
% 7.70/1.47  --clausifier_options                    --mode clausify
% 7.70/1.47  --stdin                                 false
% 7.70/1.47  --stats_out                             all
% 7.70/1.47  
% 7.70/1.47  ------ General Options
% 7.70/1.47  
% 7.70/1.47  --fof                                   false
% 7.70/1.47  --time_out_real                         305.
% 7.70/1.47  --time_out_virtual                      -1.
% 7.70/1.47  --symbol_type_check                     false
% 7.70/1.47  --clausify_out                          false
% 7.70/1.47  --sig_cnt_out                           false
% 7.70/1.47  --trig_cnt_out                          false
% 7.70/1.47  --trig_cnt_out_tolerance                1.
% 7.70/1.47  --trig_cnt_out_sk_spl                   false
% 7.70/1.47  --abstr_cl_out                          false
% 7.70/1.47  
% 7.70/1.47  ------ Global Options
% 7.70/1.47  
% 7.70/1.47  --schedule                              default
% 7.70/1.47  --add_important_lit                     false
% 7.70/1.47  --prop_solver_per_cl                    1000
% 7.70/1.47  --min_unsat_core                        false
% 7.70/1.47  --soft_assumptions                      false
% 7.70/1.47  --soft_lemma_size                       3
% 7.70/1.47  --prop_impl_unit_size                   0
% 7.70/1.47  --prop_impl_unit                        []
% 7.70/1.47  --share_sel_clauses                     true
% 7.70/1.47  --reset_solvers                         false
% 7.70/1.47  --bc_imp_inh                            [conj_cone]
% 7.70/1.47  --conj_cone_tolerance                   3.
% 7.70/1.47  --extra_neg_conj                        none
% 7.70/1.47  --large_theory_mode                     true
% 7.70/1.47  --prolific_symb_bound                   200
% 7.70/1.47  --lt_threshold                          2000
% 7.70/1.47  --clause_weak_htbl                      true
% 7.70/1.47  --gc_record_bc_elim                     false
% 7.70/1.47  
% 7.70/1.47  ------ Preprocessing Options
% 7.70/1.47  
% 7.70/1.47  --preprocessing_flag                    true
% 7.70/1.47  --time_out_prep_mult                    0.1
% 7.70/1.47  --splitting_mode                        input
% 7.70/1.47  --splitting_grd                         true
% 7.70/1.47  --splitting_cvd                         false
% 7.70/1.47  --splitting_cvd_svl                     false
% 7.70/1.47  --splitting_nvd                         32
% 7.70/1.47  --sub_typing                            true
% 7.70/1.47  --prep_gs_sim                           true
% 7.70/1.47  --prep_unflatten                        true
% 7.70/1.47  --prep_res_sim                          true
% 7.70/1.47  --prep_upred                            true
% 7.70/1.47  --prep_sem_filter                       exhaustive
% 7.70/1.47  --prep_sem_filter_out                   false
% 7.70/1.47  --pred_elim                             true
% 7.70/1.47  --res_sim_input                         true
% 7.70/1.47  --eq_ax_congr_red                       true
% 7.70/1.47  --pure_diseq_elim                       true
% 7.70/1.47  --brand_transform                       false
% 7.70/1.47  --non_eq_to_eq                          false
% 7.70/1.47  --prep_def_merge                        true
% 7.70/1.47  --prep_def_merge_prop_impl              false
% 7.70/1.47  --prep_def_merge_mbd                    true
% 7.70/1.47  --prep_def_merge_tr_red                 false
% 7.70/1.47  --prep_def_merge_tr_cl                  false
% 7.70/1.47  --smt_preprocessing                     true
% 7.70/1.47  --smt_ac_axioms                         fast
% 7.70/1.47  --preprocessed_out                      false
% 7.70/1.47  --preprocessed_stats                    false
% 7.70/1.47  
% 7.70/1.47  ------ Abstraction refinement Options
% 7.70/1.47  
% 7.70/1.47  --abstr_ref                             []
% 7.70/1.47  --abstr_ref_prep                        false
% 7.70/1.47  --abstr_ref_until_sat                   false
% 7.70/1.47  --abstr_ref_sig_restrict                funpre
% 7.70/1.47  --abstr_ref_af_restrict_to_split_sk     false
% 7.70/1.47  --abstr_ref_under                       []
% 7.70/1.47  
% 7.70/1.47  ------ SAT Options
% 7.70/1.47  
% 7.70/1.47  --sat_mode                              false
% 7.70/1.47  --sat_fm_restart_options                ""
% 7.70/1.47  --sat_gr_def                            false
% 7.70/1.47  --sat_epr_types                         true
% 7.70/1.47  --sat_non_cyclic_types                  false
% 7.70/1.47  --sat_finite_models                     false
% 7.70/1.47  --sat_fm_lemmas                         false
% 7.70/1.47  --sat_fm_prep                           false
% 7.70/1.47  --sat_fm_uc_incr                        true
% 7.70/1.47  --sat_out_model                         small
% 7.70/1.47  --sat_out_clauses                       false
% 7.70/1.47  
% 7.70/1.47  ------ QBF Options
% 7.70/1.47  
% 7.70/1.47  --qbf_mode                              false
% 7.70/1.47  --qbf_elim_univ                         false
% 7.70/1.47  --qbf_dom_inst                          none
% 7.70/1.47  --qbf_dom_pre_inst                      false
% 7.70/1.47  --qbf_sk_in                             false
% 7.70/1.47  --qbf_pred_elim                         true
% 7.70/1.47  --qbf_split                             512
% 7.70/1.47  
% 7.70/1.47  ------ BMC1 Options
% 7.70/1.47  
% 7.70/1.47  --bmc1_incremental                      false
% 7.70/1.47  --bmc1_axioms                           reachable_all
% 7.70/1.47  --bmc1_min_bound                        0
% 7.70/1.47  --bmc1_max_bound                        -1
% 7.70/1.47  --bmc1_max_bound_default                -1
% 7.70/1.47  --bmc1_symbol_reachability              true
% 7.70/1.47  --bmc1_property_lemmas                  false
% 7.70/1.47  --bmc1_k_induction                      false
% 7.70/1.47  --bmc1_non_equiv_states                 false
% 7.70/1.47  --bmc1_deadlock                         false
% 7.70/1.47  --bmc1_ucm                              false
% 7.70/1.47  --bmc1_add_unsat_core                   none
% 7.70/1.47  --bmc1_unsat_core_children              false
% 7.70/1.47  --bmc1_unsat_core_extrapolate_axioms    false
% 7.70/1.47  --bmc1_out_stat                         full
% 7.70/1.47  --bmc1_ground_init                      false
% 7.70/1.47  --bmc1_pre_inst_next_state              false
% 7.70/1.47  --bmc1_pre_inst_state                   false
% 7.70/1.47  --bmc1_pre_inst_reach_state             false
% 7.70/1.47  --bmc1_out_unsat_core                   false
% 7.70/1.47  --bmc1_aig_witness_out                  false
% 7.70/1.47  --bmc1_verbose                          false
% 7.70/1.47  --bmc1_dump_clauses_tptp                false
% 7.70/1.47  --bmc1_dump_unsat_core_tptp             false
% 7.70/1.47  --bmc1_dump_file                        -
% 7.70/1.47  --bmc1_ucm_expand_uc_limit              128
% 7.70/1.47  --bmc1_ucm_n_expand_iterations          6
% 7.70/1.47  --bmc1_ucm_extend_mode                  1
% 7.70/1.47  --bmc1_ucm_init_mode                    2
% 7.70/1.47  --bmc1_ucm_cone_mode                    none
% 7.70/1.47  --bmc1_ucm_reduced_relation_type        0
% 7.70/1.47  --bmc1_ucm_relax_model                  4
% 7.70/1.47  --bmc1_ucm_full_tr_after_sat            true
% 7.70/1.47  --bmc1_ucm_expand_neg_assumptions       false
% 7.70/1.47  --bmc1_ucm_layered_model                none
% 7.70/1.47  --bmc1_ucm_max_lemma_size               10
% 7.70/1.47  
% 7.70/1.47  ------ AIG Options
% 7.70/1.47  
% 7.70/1.47  --aig_mode                              false
% 7.70/1.47  
% 7.70/1.47  ------ Instantiation Options
% 7.70/1.47  
% 7.70/1.47  --instantiation_flag                    true
% 7.70/1.47  --inst_sos_flag                         false
% 7.70/1.47  --inst_sos_phase                        true
% 7.70/1.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.70/1.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.70/1.47  --inst_lit_sel_side                     none
% 7.70/1.47  --inst_solver_per_active                1400
% 7.70/1.47  --inst_solver_calls_frac                1.
% 7.70/1.47  --inst_passive_queue_type               priority_queues
% 7.70/1.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.70/1.47  --inst_passive_queues_freq              [25;2]
% 7.70/1.47  --inst_dismatching                      true
% 7.70/1.47  --inst_eager_unprocessed_to_passive     true
% 7.70/1.47  --inst_prop_sim_given                   true
% 7.70/1.47  --inst_prop_sim_new                     false
% 7.70/1.47  --inst_subs_new                         false
% 7.70/1.47  --inst_eq_res_simp                      false
% 7.70/1.47  --inst_subs_given                       false
% 7.70/1.47  --inst_orphan_elimination               true
% 7.70/1.47  --inst_learning_loop_flag               true
% 7.70/1.47  --inst_learning_start                   3000
% 7.70/1.47  --inst_learning_factor                  2
% 7.70/1.47  --inst_start_prop_sim_after_learn       3
% 7.70/1.47  --inst_sel_renew                        solver
% 7.70/1.47  --inst_lit_activity_flag                true
% 7.70/1.47  --inst_restr_to_given                   false
% 7.70/1.47  --inst_activity_threshold               500
% 7.70/1.47  --inst_out_proof                        true
% 7.70/1.47  
% 7.70/1.47  ------ Resolution Options
% 7.70/1.47  
% 7.70/1.47  --resolution_flag                       false
% 7.70/1.47  --res_lit_sel                           adaptive
% 7.70/1.47  --res_lit_sel_side                      none
% 7.70/1.47  --res_ordering                          kbo
% 7.70/1.47  --res_to_prop_solver                    active
% 7.70/1.47  --res_prop_simpl_new                    false
% 7.70/1.47  --res_prop_simpl_given                  true
% 7.70/1.47  --res_passive_queue_type                priority_queues
% 7.70/1.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.70/1.47  --res_passive_queues_freq               [15;5]
% 7.70/1.47  --res_forward_subs                      full
% 7.70/1.47  --res_backward_subs                     full
% 7.70/1.47  --res_forward_subs_resolution           true
% 7.70/1.47  --res_backward_subs_resolution          true
% 7.70/1.47  --res_orphan_elimination                true
% 7.70/1.47  --res_time_limit                        2.
% 7.70/1.47  --res_out_proof                         true
% 7.70/1.47  
% 7.70/1.47  ------ Superposition Options
% 7.70/1.47  
% 7.70/1.47  --superposition_flag                    true
% 7.70/1.47  --sup_passive_queue_type                priority_queues
% 7.70/1.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.70/1.47  --sup_passive_queues_freq               [8;1;4]
% 7.70/1.47  --demod_completeness_check              fast
% 7.70/1.47  --demod_use_ground                      true
% 7.70/1.47  --sup_to_prop_solver                    passive
% 7.70/1.47  --sup_prop_simpl_new                    true
% 7.70/1.47  --sup_prop_simpl_given                  true
% 7.70/1.47  --sup_fun_splitting                     false
% 7.70/1.47  --sup_smt_interval                      50000
% 7.70/1.47  
% 7.70/1.47  ------ Superposition Simplification Setup
% 7.70/1.47  
% 7.70/1.47  --sup_indices_passive                   []
% 7.70/1.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.70/1.47  --sup_full_triv                         [TrivRules;PropSubs]
% 7.70/1.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.47  --sup_full_bw                           [BwDemod]
% 7.70/1.47  --sup_immed_triv                        [TrivRules]
% 7.70/1.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.70/1.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.47  --sup_immed_bw_main                     []
% 7.70/1.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.47  --sup_input_triv                        [Unflattening;TrivRules]
% 7.70/1.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.70/1.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.70/1.47  
% 7.70/1.47  ------ Combination Options
% 7.70/1.47  
% 7.70/1.47  --comb_res_mult                         3
% 7.70/1.47  --comb_sup_mult                         2
% 7.70/1.47  --comb_inst_mult                        10
% 7.70/1.47  
% 7.70/1.47  ------ Debug Options
% 7.70/1.47  
% 7.70/1.47  --dbg_backtrace                         false
% 7.70/1.47  --dbg_dump_prop_clauses                 false
% 7.70/1.47  --dbg_dump_prop_clauses_file            -
% 7.70/1.47  --dbg_out_stat                          false
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  ------ Proving...
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  % SZS status Theorem for theBenchmark.p
% 7.70/1.47  
% 7.70/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.70/1.47  
% 7.70/1.47  fof(f14,conjecture,(
% 7.70/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f15,negated_conjecture,(
% 7.70/1.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.70/1.47    inference(negated_conjecture,[],[f14])).
% 7.70/1.47  
% 7.70/1.47  fof(f34,plain,(
% 7.70/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.70/1.47    inference(ennf_transformation,[],[f15])).
% 7.70/1.47  
% 7.70/1.47  fof(f35,plain,(
% 7.70/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.70/1.47    inference(flattening,[],[f34])).
% 7.70/1.47  
% 7.70/1.47  fof(f46,plain,(
% 7.70/1.47    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.70/1.47    introduced(choice_axiom,[])).
% 7.70/1.47  
% 7.70/1.47  fof(f45,plain,(
% 7.70/1.47    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.70/1.47    introduced(choice_axiom,[])).
% 7.70/1.47  
% 7.70/1.47  fof(f44,plain,(
% 7.70/1.47    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.70/1.47    introduced(choice_axiom,[])).
% 7.70/1.47  
% 7.70/1.47  fof(f43,plain,(
% 7.70/1.47    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.70/1.47    introduced(choice_axiom,[])).
% 7.70/1.47  
% 7.70/1.47  fof(f42,plain,(
% 7.70/1.47    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.70/1.47    introduced(choice_axiom,[])).
% 7.70/1.47  
% 7.70/1.47  fof(f41,plain,(
% 7.70/1.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.70/1.47    introduced(choice_axiom,[])).
% 7.70/1.47  
% 7.70/1.47  fof(f47,plain,(
% 7.70/1.47    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.70/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f46,f45,f44,f43,f42,f41])).
% 7.70/1.47  
% 7.70/1.47  fof(f81,plain,(
% 7.70/1.47    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f7,axiom,(
% 7.70/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f22,plain,(
% 7.70/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.70/1.47    inference(ennf_transformation,[],[f7])).
% 7.70/1.47  
% 7.70/1.47  fof(f56,plain,(
% 7.70/1.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.70/1.47    inference(cnf_transformation,[],[f22])).
% 7.70/1.47  
% 7.70/1.47  fof(f2,axiom,(
% 7.70/1.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f17,plain,(
% 7.70/1.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.70/1.47    inference(ennf_transformation,[],[f2])).
% 7.70/1.47  
% 7.70/1.47  fof(f50,plain,(
% 7.70/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f17])).
% 7.70/1.47  
% 7.70/1.47  fof(f3,axiom,(
% 7.70/1.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f51,plain,(
% 7.70/1.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f3])).
% 7.70/1.47  
% 7.70/1.47  fof(f1,axiom,(
% 7.70/1.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f36,plain,(
% 7.70/1.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.70/1.47    inference(nnf_transformation,[],[f1])).
% 7.70/1.47  
% 7.70/1.47  fof(f49,plain,(
% 7.70/1.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.70/1.47    inference(cnf_transformation,[],[f36])).
% 7.70/1.47  
% 7.70/1.47  fof(f5,axiom,(
% 7.70/1.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f19,plain,(
% 7.70/1.47    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.70/1.47    inference(ennf_transformation,[],[f5])).
% 7.70/1.47  
% 7.70/1.47  fof(f53,plain,(
% 7.70/1.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f19])).
% 7.70/1.47  
% 7.70/1.47  fof(f74,plain,(
% 7.70/1.47    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f4,axiom,(
% 7.70/1.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f18,plain,(
% 7.70/1.47    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.70/1.47    inference(ennf_transformation,[],[f4])).
% 7.70/1.47  
% 7.70/1.47  fof(f52,plain,(
% 7.70/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.70/1.47    inference(cnf_transformation,[],[f18])).
% 7.70/1.47  
% 7.70/1.47  fof(f78,plain,(
% 7.70/1.47    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f11,axiom,(
% 7.70/1.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f28,plain,(
% 7.70/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.70/1.47    inference(ennf_transformation,[],[f11])).
% 7.70/1.47  
% 7.70/1.47  fof(f29,plain,(
% 7.70/1.47    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.70/1.47    inference(flattening,[],[f28])).
% 7.70/1.47  
% 7.70/1.47  fof(f62,plain,(
% 7.70/1.47    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f29])).
% 7.70/1.47  
% 7.70/1.47  fof(f76,plain,(
% 7.70/1.47    v1_funct_1(sK4)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f79,plain,(
% 7.70/1.47    v1_funct_1(sK5)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f12,axiom,(
% 7.70/1.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f30,plain,(
% 7.70/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.47    inference(ennf_transformation,[],[f12])).
% 7.70/1.47  
% 7.70/1.47  fof(f31,plain,(
% 7.70/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.47    inference(flattening,[],[f30])).
% 7.70/1.47  
% 7.70/1.47  fof(f39,plain,(
% 7.70/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.47    inference(nnf_transformation,[],[f31])).
% 7.70/1.47  
% 7.70/1.47  fof(f40,plain,(
% 7.70/1.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.70/1.47    inference(flattening,[],[f39])).
% 7.70/1.47  
% 7.70/1.47  fof(f64,plain,(
% 7.70/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f40])).
% 7.70/1.47  
% 7.70/1.47  fof(f86,plain,(
% 7.70/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(equality_resolution,[],[f64])).
% 7.70/1.47  
% 7.70/1.47  fof(f13,axiom,(
% 7.70/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f32,plain,(
% 7.70/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.70/1.47    inference(ennf_transformation,[],[f13])).
% 7.70/1.47  
% 7.70/1.47  fof(f33,plain,(
% 7.70/1.47    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.47    inference(flattening,[],[f32])).
% 7.70/1.47  
% 7.70/1.47  fof(f66,plain,(
% 7.70/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f33])).
% 7.70/1.47  
% 7.70/1.47  fof(f67,plain,(
% 7.70/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f33])).
% 7.70/1.47  
% 7.70/1.47  fof(f68,plain,(
% 7.70/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f33])).
% 7.70/1.47  
% 7.70/1.47  fof(f70,plain,(
% 7.70/1.47    ~v1_xboole_0(sK1)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f73,plain,(
% 7.70/1.47    ~v1_xboole_0(sK3)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f80,plain,(
% 7.70/1.47    v1_funct_2(sK5,sK3,sK1)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f71,plain,(
% 7.70/1.47    ~v1_xboole_0(sK2)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f77,plain,(
% 7.70/1.47    v1_funct_2(sK4,sK2,sK1)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f48,plain,(
% 7.70/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f36])).
% 7.70/1.47  
% 7.70/1.47  fof(f6,axiom,(
% 7.70/1.47    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.70/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.70/1.47  
% 7.70/1.47  fof(f20,plain,(
% 7.70/1.47    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.70/1.47    inference(ennf_transformation,[],[f6])).
% 7.70/1.47  
% 7.70/1.47  fof(f21,plain,(
% 7.70/1.47    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.47    inference(flattening,[],[f20])).
% 7.70/1.47  
% 7.70/1.47  fof(f37,plain,(
% 7.70/1.47    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.70/1.47    inference(nnf_transformation,[],[f21])).
% 7.70/1.47  
% 7.70/1.47  fof(f54,plain,(
% 7.70/1.47    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f37])).
% 7.70/1.47  
% 7.70/1.47  fof(f75,plain,(
% 7.70/1.47    r1_subset_1(sK2,sK3)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f69,plain,(
% 7.70/1.47    ~v1_xboole_0(sK0)),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f72,plain,(
% 7.70/1.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f82,plain,(
% 7.70/1.47    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.70/1.47    inference(cnf_transformation,[],[f47])).
% 7.70/1.47  
% 7.70/1.47  fof(f63,plain,(
% 7.70/1.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(cnf_transformation,[],[f40])).
% 7.70/1.47  
% 7.70/1.47  fof(f87,plain,(
% 7.70/1.47    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.70/1.47    inference(equality_resolution,[],[f63])).
% 7.70/1.47  
% 7.70/1.47  cnf(c_22,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.70/1.47      inference(cnf_transformation,[],[f81]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_855,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_22]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1309,plain,
% 7.70/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_8,plain,
% 7.70/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | v1_relat_1(X0) ),
% 7.70/1.47      inference(cnf_transformation,[],[f56]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_862,plain,
% 7.70/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.70/1.47      | v1_relat_1(X0_54) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_8]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1303,plain,
% 7.70/1.47      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.70/1.47      | v1_relat_1(X0_54) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2090,plain,
% 7.70/1.47      ( v1_relat_1(sK5) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1309,c_1303]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2,plain,
% 7.70/1.47      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.70/1.47      inference(cnf_transformation,[],[f50]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_3,plain,
% 7.70/1.47      ( r1_tarski(k1_xboole_0,X0) ),
% 7.70/1.47      inference(cnf_transformation,[],[f51]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_452,plain,
% 7.70/1.47      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 7.70/1.47      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_453,plain,
% 7.70/1.47      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.70/1.47      inference(unflattening,[status(thm)],[c_452]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_841,plain,
% 7.70/1.47      ( k3_xboole_0(k1_xboole_0,X0_54) = k1_xboole_0 ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_453]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_0,plain,
% 7.70/1.47      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.70/1.47      inference(cnf_transformation,[],[f49]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_257,plain,
% 7.70/1.47      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.70/1.47      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_5,plain,
% 7.70/1.47      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.70/1.47      | ~ v1_relat_1(X1)
% 7.70/1.47      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.70/1.47      inference(cnf_transformation,[],[f53]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_536,plain,
% 7.70/1.47      ( ~ v1_relat_1(X0)
% 7.70/1.47      | X1 != X2
% 7.70/1.47      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.70/1.47      | k3_xboole_0(X2,X3) != k1_xboole_0
% 7.70/1.47      | k1_relat_1(X0) != X3 ),
% 7.70/1.47      inference(resolution_lifted,[status(thm)],[c_257,c_5]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_537,plain,
% 7.70/1.47      ( ~ v1_relat_1(X0)
% 7.70/1.47      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.70/1.47      | k3_xboole_0(X1,k1_relat_1(X0)) != k1_xboole_0 ),
% 7.70/1.47      inference(unflattening,[status(thm)],[c_536]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_840,plain,
% 7.70/1.47      ( ~ v1_relat_1(X0_54)
% 7.70/1.47      | k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.70/1.47      | k3_xboole_0(X1_54,k1_relat_1(X0_54)) != k1_xboole_0 ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_537]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1323,plain,
% 7.70/1.47      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.70/1.47      | k3_xboole_0(X1_54,k1_relat_1(X0_54)) != k1_xboole_0
% 7.70/1.47      | v1_relat_1(X0_54) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_18550,plain,
% 7.70/1.47      ( k7_relat_1(X0_54,k1_xboole_0) = k1_xboole_0
% 7.70/1.47      | v1_relat_1(X0_54) != iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_841,c_1323]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_18619,plain,
% 7.70/1.47      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2090,c_18550]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_29,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.70/1.47      inference(cnf_transformation,[],[f74]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_849,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_29]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1315,plain,
% 7.70/1.47      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_4,plain,
% 7.70/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.70/1.47      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.70/1.47      inference(cnf_transformation,[],[f52]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_863,plain,
% 7.70/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.70/1.47      | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_4]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1302,plain,
% 7.70/1.47      ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2137,plain,
% 7.70/1.47      ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1315,c_1302]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_25,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.70/1.47      inference(cnf_transformation,[],[f78]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_852,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_25]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1312,plain,
% 7.70/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_14,plain,
% 7.70/1.47      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.70/1.47      inference(cnf_transformation,[],[f62]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_861,plain,
% 7.70/1.47      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.70/1.47      | ~ v1_funct_1(X0_54)
% 7.70/1.47      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_14]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1304,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.70/1.47      | v1_funct_1(X2_54) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2215,plain,
% 7.70/1.47      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 7.70/1.47      | v1_funct_1(sK4) != iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1312,c_1304]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_27,negated_conjecture,
% 7.70/1.47      ( v1_funct_1(sK4) ),
% 7.70/1.47      inference(cnf_transformation,[],[f76]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1702,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.70/1.47      | ~ v1_funct_1(sK4)
% 7.70/1.47      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_861]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1860,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.70/1.47      | ~ v1_funct_1(sK4)
% 7.70/1.47      | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_1702]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2849,plain,
% 7.70/1.47      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_2215,c_27,c_25,c_1860]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2214,plain,
% 7.70/1.47      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 7.70/1.47      | v1_funct_1(sK5) != iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1309,c_1304]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_24,negated_conjecture,
% 7.70/1.47      ( v1_funct_1(sK5) ),
% 7.70/1.47      inference(cnf_transformation,[],[f79]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1697,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.70/1.47      | ~ v1_funct_1(sK5)
% 7.70/1.47      | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_861]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1855,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.70/1.47      | ~ v1_funct_1(sK5)
% 7.70/1.47      | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_1697]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2810,plain,
% 7.70/1.47      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_2214,c_24,c_22,c_1855]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.70/1.47      inference(cnf_transformation,[],[f86]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_20,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f66]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_19,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f67]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_18,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f68]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_199,plain,
% 7.70/1.47      ( ~ v1_funct_1(X3)
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_16,c_20,c_19,c_18]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_200,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_199]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_842,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.70/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.70/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.70/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.70/1.47      | ~ v1_funct_1(X0_54)
% 7.70/1.47      | ~ v1_funct_1(X3_54)
% 7.70/1.47      | v1_xboole_0(X2_54)
% 7.70/1.47      | v1_xboole_0(X1_54)
% 7.70/1.47      | v1_xboole_0(X4_54)
% 7.70/1.47      | v1_xboole_0(X5_54)
% 7.70/1.47      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_200]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1322,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.70/1.47      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.70/1.47      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.70/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.70/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.70/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_5413,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.70/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.70/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.70/1.47      | v1_funct_1(sK5) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2810,c_1322]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_33,negated_conjecture,
% 7.70/1.47      ( ~ v1_xboole_0(sK1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f70]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_36,plain,
% 7.70/1.47      ( v1_xboole_0(sK1) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_30,negated_conjecture,
% 7.70/1.47      ( ~ v1_xboole_0(sK3) ),
% 7.70/1.47      inference(cnf_transformation,[],[f73]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_39,plain,
% 7.70/1.47      ( v1_xboole_0(sK3) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_45,plain,
% 7.70/1.47      ( v1_funct_1(sK5) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_23,negated_conjecture,
% 7.70/1.47      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f80]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_46,plain,
% 7.70/1.47      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_47,plain,
% 7.70/1.47      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16466,plain,
% 7.70/1.47      ( v1_funct_1(X1_54) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.70/1.47      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.70/1.47      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_5413,c_36,c_39,c_45,c_46,c_47]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16467,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.70/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_16466]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16482,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.70/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(sK4) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2849,c_16467]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_32,negated_conjecture,
% 7.70/1.47      ( ~ v1_xboole_0(sK2) ),
% 7.70/1.47      inference(cnf_transformation,[],[f71]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_37,plain,
% 7.70/1.47      ( v1_xboole_0(sK2) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_42,plain,
% 7.70/1.47      ( v1_funct_1(sK4) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_26,negated_conjecture,
% 7.70/1.47      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f77]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_43,plain,
% 7.70/1.47      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_44,plain,
% 7.70/1.47      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16616,plain,
% 7.70/1.47      ( v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_16482,c_37,c_42,c_43,c_44]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16617,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_16616]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16627,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2137,c_16617]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1,plain,
% 7.70/1.47      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.70/1.47      inference(cnf_transformation,[],[f48]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_259,plain,
% 7.70/1.47      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.70/1.47      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_7,plain,
% 7.70/1.47      ( ~ r1_subset_1(X0,X1)
% 7.70/1.47      | r1_xboole_0(X0,X1)
% 7.70/1.47      | v1_xboole_0(X0)
% 7.70/1.47      | v1_xboole_0(X1) ),
% 7.70/1.47      inference(cnf_transformation,[],[f54]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_28,negated_conjecture,
% 7.70/1.47      ( r1_subset_1(sK2,sK3) ),
% 7.70/1.47      inference(cnf_transformation,[],[f75]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_522,plain,
% 7.70/1.47      ( r1_xboole_0(X0,X1)
% 7.70/1.47      | v1_xboole_0(X0)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | sK3 != X1
% 7.70/1.47      | sK2 != X0 ),
% 7.70/1.47      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_523,plain,
% 7.70/1.47      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.70/1.47      inference(unflattening,[status(thm)],[c_522]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_525,plain,
% 7.70/1.47      ( r1_xboole_0(sK2,sK3) ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_523,c_32,c_30]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_551,plain,
% 7.70/1.47      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 7.70/1.47      inference(resolution_lifted,[status(thm)],[c_259,c_525]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_552,plain,
% 7.70/1.47      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.70/1.47      inference(unflattening,[status(thm)],[c_551]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_839,plain,
% 7.70/1.47      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_552]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16628,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(light_normalisation,[status(thm)],[c_16627,c_839]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_859,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.70/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.70/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.70/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.70/1.47      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
% 7.70/1.47      | ~ v1_funct_1(X0_54)
% 7.70/1.47      | ~ v1_funct_1(X3_54)
% 7.70/1.47      | v1_xboole_0(X2_54)
% 7.70/1.47      | v1_xboole_0(X1_54)
% 7.70/1.47      | v1_xboole_0(X4_54)
% 7.70/1.47      | v1_xboole_0(X5_54) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_18]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1306,plain,
% 7.70/1.47      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.70/1.47      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.70/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 7.70/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.70/1.47      | v1_funct_1(X3_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X5_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2334,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.70/1.47      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.70/1.47      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.70/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.70/1.47      | v1_funct_1(X4_54) != iProver_top
% 7.70/1.47      | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1306,c_1304]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_857,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.70/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.70/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.70/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.70/1.47      | ~ v1_funct_1(X0_54)
% 7.70/1.47      | ~ v1_funct_1(X3_54)
% 7.70/1.47      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
% 7.70/1.47      | v1_xboole_0(X2_54)
% 7.70/1.47      | v1_xboole_0(X1_54)
% 7.70/1.47      | v1_xboole_0(X4_54)
% 7.70/1.47      | v1_xboole_0(X5_54) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_20]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1308,plain,
% 7.70/1.47      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.70/1.47      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.70/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.70/1.47      | v1_funct_1(X0_54) != iProver_top
% 7.70/1.47      | v1_funct_1(X3_54) != iProver_top
% 7.70/1.47      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 7.70/1.47      | v1_xboole_0(X5_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6043,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.70/1.47      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.70/1.47      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.70/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.70/1.47      | v1_funct_1(X4_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(forward_subsumption_resolution,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_2334,c_1308]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6047,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.70/1.47      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.70/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.70/1.47      | v1_funct_1(sK5) != iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1309,c_6043]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6154,plain,
% 7.70/1.47      ( v1_funct_1(X2_54) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.70/1.47      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_6047,c_36,c_39,c_45,c_46]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6155,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.70/1.47      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_6154]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6169,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.70/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(sK4) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1312,c_6155]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6519,plain,
% 7.70/1.47      ( v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_6169,c_37,c_42,c_43]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6520,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_6519]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6529,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_1315,c_6520]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_34,negated_conjecture,
% 7.70/1.47      ( ~ v1_xboole_0(sK0) ),
% 7.70/1.47      inference(cnf_transformation,[],[f69]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_35,plain,
% 7.70/1.47      ( v1_xboole_0(sK0) != iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_31,negated_conjecture,
% 7.70/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.70/1.47      inference(cnf_transformation,[],[f72]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_38,plain,
% 7.70/1.47      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6534,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_6529,c_35,c_38]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16629,plain,
% 7.70/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_16628,c_2137,c_6534]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16630,plain,
% 7.70/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(light_normalisation,[status(thm)],[c_16629,c_839]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_21,negated_conjecture,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.70/1.47      inference(cnf_transformation,[],[f82]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_856,negated_conjecture,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_21]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2208,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_2137,c_856]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2209,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.70/1.47      inference(light_normalisation,[status(thm)],[c_2208,c_839]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2853,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_2209,c_2810,c_2849]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6538,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_6534,c_2853]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_6539,plain,
% 7.70/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.70/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_6538,c_6534]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_17,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.70/1.47      inference(cnf_transformation,[],[f87]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_192,plain,
% 7.70/1.47      ( ~ v1_funct_1(X3)
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_17,c_20,c_19,c_18]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_193,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0,X1,X2)
% 7.70/1.47      | ~ v1_funct_2(X3,X4,X2)
% 7.70/1.47      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.70/1.47      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.70/1.47      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.70/1.47      | ~ v1_funct_1(X0)
% 7.70/1.47      | ~ v1_funct_1(X3)
% 7.70/1.47      | v1_xboole_0(X1)
% 7.70/1.47      | v1_xboole_0(X2)
% 7.70/1.47      | v1_xboole_0(X4)
% 7.70/1.47      | v1_xboole_0(X5)
% 7.70/1.47      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_192]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_843,plain,
% 7.70/1.47      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.70/1.47      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.70/1.47      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.70/1.47      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.70/1.47      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.70/1.47      | ~ v1_funct_1(X0_54)
% 7.70/1.47      | ~ v1_funct_1(X3_54)
% 7.70/1.47      | v1_xboole_0(X2_54)
% 7.70/1.47      | v1_xboole_0(X1_54)
% 7.70/1.47      | v1_xboole_0(X4_54)
% 7.70/1.47      | v1_xboole_0(X5_54)
% 7.70/1.47      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.70/1.47      inference(subtyping,[status(esa)],[c_193]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1321,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.70/1.47      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.70/1.47      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.70/1.47      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.70/1.47      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.70/1.47      | v1_funct_1(X2_54) != iProver_top
% 7.70/1.47      | v1_funct_1(X5_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X3_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X1_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X4_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_3092,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.70/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.70/1.47      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.70/1.47      | v1_funct_1(sK5) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK1) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK3) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2810,c_1321]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_9711,plain,
% 7.70/1.47      ( v1_funct_1(X1_54) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.70/1.47      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.70/1.47      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_3092,c_36,c_39,c_45,c_46,c_47]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_9712,plain,
% 7.70/1.47      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.70/1.47      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.70/1.47      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(X1_54) != iProver_top
% 7.70/1.47      | v1_xboole_0(X2_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_9711]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_9727,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.70/1.47      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.70/1.47      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_funct_1(sK4) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | v1_xboole_0(sK2) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2849,c_9712]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10372,plain,
% 7.70/1.47      ( v1_xboole_0(X0_54) = iProver_top
% 7.70/1.47      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_9727,c_37,c_42,c_43,c_44]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10373,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.70/1.47      | v1_xboole_0(X0_54) = iProver_top ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_10372]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10383,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(superposition,[status(thm)],[c_2137,c_10373]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10384,plain,
% 7.70/1.47      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(light_normalisation,[status(thm)],[c_10383,c_839]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10385,plain,
% 7.70/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_10384,c_2137,c_6534]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10386,plain,
% 7.70/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.70/1.47      | v1_xboole_0(sK0) = iProver_top ),
% 7.70/1.47      inference(light_normalisation,[status(thm)],[c_10385,c_839]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10387,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.70/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.70/1.47      | v1_xboole_0(sK0)
% 7.70/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_10386]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10389,plain,
% 7.70/1.47      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 7.70/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_10386,c_34,c_31,c_29,c_10387]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_10390,plain,
% 7.70/1.47      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(renaming,[status(thm)],[c_10389]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16631,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.70/1.47      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.70/1.47      | v1_xboole_0(sK0)
% 7.70/1.47      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(predicate_to_equality_rev,[status(thm)],[c_16630]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_16702,plain,
% 7.70/1.47      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.70/1.47      inference(global_propositional_subsumption,
% 7.70/1.47                [status(thm)],
% 7.70/1.47                [c_16630,c_34,c_31,c_29,c_6539,c_10390,c_16631]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_18684,plain,
% 7.70/1.47      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.70/1.47      inference(demodulation,[status(thm)],[c_18619,c_16702]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2045,plain,
% 7.70/1.47      ( k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) = k1_xboole_0 ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_841]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1789,plain,
% 7.70/1.47      ( ~ v1_relat_1(sK4)
% 7.70/1.47      | k7_relat_1(sK4,X0_54) = k1_xboole_0
% 7.70/1.47      | k3_xboole_0(X0_54,k1_relat_1(sK4)) != k1_xboole_0 ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_840]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_2044,plain,
% 7.70/1.47      ( ~ v1_relat_1(sK4)
% 7.70/1.47      | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0
% 7.70/1.47      | k3_xboole_0(k1_xboole_0,k1_relat_1(sK4)) != k1_xboole_0 ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_1789]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(c_1624,plain,
% 7.70/1.47      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.70/1.47      | v1_relat_1(sK4) ),
% 7.70/1.47      inference(instantiation,[status(thm)],[c_862]) ).
% 7.70/1.47  
% 7.70/1.47  cnf(contradiction,plain,
% 7.70/1.47      ( $false ),
% 7.70/1.47      inference(minisat,[status(thm)],[c_18684,c_2045,c_2044,c_1624,c_25]) ).
% 7.70/1.47  
% 7.70/1.47  
% 7.70/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.70/1.47  
% 7.70/1.47  ------                               Statistics
% 7.70/1.47  
% 7.70/1.47  ------ General
% 7.70/1.47  
% 7.70/1.47  abstr_ref_over_cycles:                  0
% 7.70/1.47  abstr_ref_under_cycles:                 0
% 7.70/1.47  gc_basic_clause_elim:                   0
% 7.70/1.47  forced_gc_time:                         0
% 7.70/1.47  parsing_time:                           0.012
% 7.70/1.47  unif_index_cands_time:                  0.
% 7.70/1.47  unif_index_add_time:                    0.
% 7.70/1.47  orderings_time:                         0.
% 7.70/1.47  out_proof_time:                         0.018
% 7.70/1.47  total_time:                             0.96
% 7.70/1.47  num_of_symbols:                         59
% 7.70/1.47  num_of_terms:                           33901
% 7.70/1.47  
% 7.70/1.47  ------ Preprocessing
% 7.70/1.47  
% 7.70/1.47  num_of_splits:                          0
% 7.70/1.47  num_of_split_atoms:                     0
% 7.70/1.47  num_of_reused_defs:                     0
% 7.70/1.47  num_eq_ax_congr_red:                    16
% 7.70/1.47  num_of_sem_filtered_clauses:            1
% 7.70/1.47  num_of_subtypes:                        2
% 7.70/1.47  monotx_restored_types:                  0
% 7.70/1.47  sat_num_of_epr_types:                   0
% 7.70/1.47  sat_num_of_non_cyclic_types:            0
% 7.70/1.47  sat_guarded_non_collapsed_types:        1
% 7.70/1.47  num_pure_diseq_elim:                    0
% 7.70/1.47  simp_replaced_by:                       0
% 7.70/1.47  res_preprocessed:                       146
% 7.70/1.47  prep_upred:                             0
% 7.70/1.47  prep_unflattend:                        14
% 7.70/1.47  smt_new_axioms:                         0
% 7.70/1.47  pred_elim_cands:                        5
% 7.70/1.47  pred_elim:                              5
% 7.70/1.47  pred_elim_cl:                           7
% 7.70/1.47  pred_elim_cycles:                       9
% 7.70/1.47  merged_defs:                            2
% 7.70/1.47  merged_defs_ncl:                        0
% 7.70/1.47  bin_hyper_res:                          2
% 7.70/1.47  prep_cycles:                            4
% 7.70/1.47  pred_elim_time:                         0.006
% 7.70/1.47  splitting_time:                         0.
% 7.70/1.47  sem_filter_time:                        0.
% 7.70/1.47  monotx_time:                            0.
% 7.70/1.47  subtype_inf_time:                       0.001
% 7.70/1.47  
% 7.70/1.47  ------ Problem properties
% 7.70/1.47  
% 7.70/1.47  clauses:                                27
% 7.70/1.47  conjectures:                            13
% 7.70/1.47  epr:                                    8
% 7.70/1.47  horn:                                   20
% 7.70/1.47  ground:                                 14
% 7.70/1.47  unary:                                  14
% 7.70/1.47  binary:                                 2
% 7.70/1.47  lits:                                   119
% 7.70/1.47  lits_eq:                                18
% 7.70/1.47  fd_pure:                                0
% 7.70/1.47  fd_pseudo:                              0
% 7.70/1.47  fd_cond:                                0
% 7.70/1.47  fd_pseudo_cond:                         1
% 7.70/1.47  ac_symbols:                             0
% 7.70/1.47  
% 7.70/1.47  ------ Propositional Solver
% 7.70/1.47  
% 7.70/1.47  prop_solver_calls:                      30
% 7.70/1.47  prop_fast_solver_calls:                 3495
% 7.70/1.47  smt_solver_calls:                       0
% 7.70/1.47  smt_fast_solver_calls:                  0
% 7.70/1.47  prop_num_of_clauses:                    7059
% 7.70/1.47  prop_preprocess_simplified:             14264
% 7.70/1.47  prop_fo_subsumed:                       262
% 7.70/1.47  prop_solver_time:                       0.
% 7.70/1.47  smt_solver_time:                        0.
% 7.70/1.47  smt_fast_solver_time:                   0.
% 7.70/1.47  prop_fast_solver_time:                  0.
% 7.70/1.47  prop_unsat_core_time:                   0.001
% 7.70/1.47  
% 7.70/1.47  ------ QBF
% 7.70/1.47  
% 7.70/1.47  qbf_q_res:                              0
% 7.70/1.47  qbf_num_tautologies:                    0
% 7.70/1.47  qbf_prep_cycles:                        0
% 7.70/1.47  
% 7.70/1.47  ------ BMC1
% 7.70/1.47  
% 7.70/1.47  bmc1_current_bound:                     -1
% 7.70/1.47  bmc1_last_solved_bound:                 -1
% 7.70/1.47  bmc1_unsat_core_size:                   -1
% 7.70/1.47  bmc1_unsat_core_parents_size:           -1
% 7.70/1.47  bmc1_merge_next_fun:                    0
% 7.70/1.47  bmc1_unsat_core_clauses_time:           0.
% 7.70/1.47  
% 7.70/1.47  ------ Instantiation
% 7.70/1.47  
% 7.70/1.47  inst_num_of_clauses:                    1646
% 7.70/1.47  inst_num_in_passive:                    769
% 7.70/1.47  inst_num_in_active:                     768
% 7.70/1.47  inst_num_in_unprocessed:                109
% 7.70/1.47  inst_num_of_loops:                      780
% 7.70/1.47  inst_num_of_learning_restarts:          0
% 7.70/1.47  inst_num_moves_active_passive:          7
% 7.70/1.47  inst_lit_activity:                      0
% 7.70/1.47  inst_lit_activity_moves:                0
% 7.70/1.47  inst_num_tautologies:                   0
% 7.70/1.47  inst_num_prop_implied:                  0
% 7.70/1.48  inst_num_existing_simplified:           0
% 7.70/1.48  inst_num_eq_res_simplified:             0
% 7.70/1.48  inst_num_child_elim:                    0
% 7.70/1.48  inst_num_of_dismatching_blockings:      206
% 7.70/1.48  inst_num_of_non_proper_insts:           1344
% 7.70/1.48  inst_num_of_duplicates:                 0
% 7.70/1.48  inst_inst_num_from_inst_to_res:         0
% 7.70/1.48  inst_dismatching_checking_time:         0.
% 7.70/1.48  
% 7.70/1.48  ------ Resolution
% 7.70/1.48  
% 7.70/1.48  res_num_of_clauses:                     0
% 7.70/1.48  res_num_in_passive:                     0
% 7.70/1.48  res_num_in_active:                      0
% 7.70/1.48  res_num_of_loops:                       150
% 7.70/1.48  res_forward_subset_subsumed:            55
% 7.70/1.48  res_backward_subset_subsumed:           2
% 7.70/1.48  res_forward_subsumed:                   0
% 7.70/1.48  res_backward_subsumed:                  0
% 7.70/1.48  res_forward_subsumption_resolution:     1
% 7.70/1.48  res_backward_subsumption_resolution:    0
% 7.70/1.48  res_clause_to_clause_subsumption:       2585
% 7.70/1.48  res_orphan_elimination:                 0
% 7.70/1.48  res_tautology_del:                      45
% 7.70/1.48  res_num_eq_res_simplified:              0
% 7.70/1.48  res_num_sel_changes:                    0
% 7.70/1.48  res_moves_from_active_to_pass:          0
% 7.70/1.48  
% 7.70/1.48  ------ Superposition
% 7.70/1.48  
% 7.70/1.48  sup_time_total:                         0.
% 7.70/1.48  sup_time_generating:                    0.
% 7.70/1.48  sup_time_sim_full:                      0.
% 7.70/1.48  sup_time_sim_immed:                     0.
% 7.70/1.48  
% 7.70/1.48  sup_num_of_clauses:                     290
% 7.70/1.48  sup_num_in_active:                      146
% 7.70/1.48  sup_num_in_passive:                     144
% 7.70/1.48  sup_num_of_loops:                       154
% 7.70/1.48  sup_fw_superposition:                   273
% 7.70/1.48  sup_bw_superposition:                   51
% 7.70/1.48  sup_immediate_simplified:               155
% 7.70/1.48  sup_given_eliminated:                   0
% 7.70/1.48  comparisons_done:                       0
% 7.70/1.48  comparisons_avoided:                    0
% 7.70/1.48  
% 7.70/1.48  ------ Simplifications
% 7.70/1.48  
% 7.70/1.48  
% 7.70/1.48  sim_fw_subset_subsumed:                 1
% 7.70/1.48  sim_bw_subset_subsumed:                 0
% 7.70/1.48  sim_fw_subsumed:                        23
% 7.70/1.48  sim_bw_subsumed:                        10
% 7.70/1.48  sim_fw_subsumption_res:                 11
% 7.70/1.48  sim_bw_subsumption_res:                 1
% 7.70/1.48  sim_tautology_del:                      0
% 7.70/1.48  sim_eq_tautology_del:                   5
% 7.70/1.48  sim_eq_res_simp:                        0
% 7.70/1.48  sim_fw_demodulated:                     98
% 7.70/1.48  sim_bw_demodulated:                     8
% 7.70/1.48  sim_light_normalised:                   48
% 7.70/1.48  sim_joinable_taut:                      0
% 7.70/1.48  sim_joinable_simp:                      0
% 7.70/1.48  sim_ac_normalised:                      0
% 7.70/1.48  sim_smt_subsumption:                    0
% 7.70/1.48  
%------------------------------------------------------------------------------
