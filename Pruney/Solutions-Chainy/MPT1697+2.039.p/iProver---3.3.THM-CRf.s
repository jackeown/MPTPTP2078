%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:30 EST 2020

% Result     : Theorem 7.91s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  206 (1476 expanded)
%              Number of clauses        :  129 ( 453 expanded)
%              Number of leaves         :   21 ( 528 expanded)
%              Depth                    :   23
%              Number of atoms          : 1081 (16842 expanded)
%              Number of equality atoms :  401 (4110 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    inference(ennf_transformation,[],[f17])).

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

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f65,plain,(
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
    inference(equality_resolution,[],[f65])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f67,plain,(
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

fof(f68,plain,(
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

fof(f69,plain,(
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

fof(f71,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f64,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f83,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1020,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1811,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1043,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1792,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1043])).

cnf(c_2565,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
    inference(superposition,[status(thm)],[c_1811,c_1792])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1023,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1808,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1032,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1800,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1032])).

cnf(c_3759,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_1800])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3835,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3759,c_43])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1026,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1805,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_3758,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1800])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3789,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3758,c_46])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_191,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_21,c_20,c_19])).

cnf(c_192,plain,
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
    inference(renaming,[status(thm)],[c_191])).

cnf(c_1013,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_1818,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_6066,plain,
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
    inference(superposition,[status(thm)],[c_3789,c_1818])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11657,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6066,c_37,c_40,c_46,c_47,c_48])).

cnf(c_11658,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_11657])).

cnf(c_11664,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_11658])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1041,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1972,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_54))
    | ~ v1_xboole_0(X0_54)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_1973,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1972])).

cnf(c_12914,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11664,c_38,c_43,c_44,c_45,c_1973])).

cnf(c_12915,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12914])).

cnf(c_12920,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_12915])).

cnf(c_11,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_472,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_473,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_33,c_31])).

cnf(c_1012,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_1819,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1044,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1791,plain,
    ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1044])).

cnf(c_2937,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1819,c_1791])).

cnf(c_5,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1040,plain,
    ( k9_relat_1(k1_xboole_0,X0_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1038,plain,
    ( r1_xboole_0(k1_relat_1(X0_54),X1_54)
    | ~ v1_relat_1(X0_54)
    | k9_relat_1(X0_54,X1_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1796,plain,
    ( k9_relat_1(X0_54,X1_54) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_54),X1_54) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1038])).

cnf(c_3681,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0_54) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_1796])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1036,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3682,plain,
    ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3681,c_1036])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1042,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1793,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1042])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1797,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_3445,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_1797])).

cnf(c_3703,plain,
    ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3682,c_3445])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_xboole_0(X3,X1)
    | k5_relset_1(X1,X2,X0,X3) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1033,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ r1_xboole_0(X3_54,X1_54)
    | k5_relset_1(X1_54,X2_54,X0_54,X3_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1799,plain,
    ( k5_relset_1(X0_54,X1_54,X2_54,X3_54) = k1_xboole_0
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | r1_xboole_0(X3_54,X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_3712,plain,
    ( k5_relset_1(sK3,sK1,sK5,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_1799])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1034,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | k5_relset_1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1798,plain,
    ( k5_relset_1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1034])).

cnf(c_3674,plain,
    ( k5_relset_1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(superposition,[status(thm)],[c_1805,c_1798])).

cnf(c_3717,plain,
    ( k7_relat_1(sK5,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3712,c_3674])).

cnf(c_3894,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3703,c_3717])).

cnf(c_12921,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12920,c_2937,c_3894])).

cnf(c_12922,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12921,c_2565])).

cnf(c_3713,plain,
    ( k5_relset_1(sK2,sK1,sK4,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1808,c_1799])).

cnf(c_3675,plain,
    ( k5_relset_1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_1808,c_1798])).

cnf(c_3716,plain,
    ( k7_relat_1(sK4,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3713,c_3675])).

cnf(c_3891,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3703,c_3716])).

cnf(c_12923,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12922,c_2937,c_3891])).

cnf(c_12924,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12923])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_184,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21,c_20,c_19])).

cnf(c_185,plain,
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
    inference(renaming,[status(thm)],[c_184])).

cnf(c_1014,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_1817,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1014])).

cnf(c_4391,plain,
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
    inference(superposition,[status(thm)],[c_3789,c_1817])).

cnf(c_5761,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4391,c_37,c_40,c_46,c_47,c_48])).

cnf(c_5762,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_5761])).

cnf(c_5768,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3835,c_5762])).

cnf(c_5883,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5768,c_38,c_43,c_44,c_45,c_1973])).

cnf(c_5884,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5883])).

cnf(c_5889,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2565,c_5884])).

cnf(c_5890,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5889,c_2937,c_3894])).

cnf(c_5891,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5890,c_2565])).

cnf(c_5892,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5891,c_2937,c_3891])).

cnf(c_5893,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5892])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1027,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2753,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2565,c_1027])).

cnf(c_3623,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2937,c_2753])).

cnf(c_3838,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3623,c_3789,c_3835])).

cnf(c_4254,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3891,c_3838])).

cnf(c_4255,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4254,c_3894])).

cnf(c_4256,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_4255])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12924,c_5893,c_4256,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:22:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.91/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.91/1.49  
% 7.91/1.49  ------  iProver source info
% 7.91/1.49  
% 7.91/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.91/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.91/1.49  git: non_committed_changes: false
% 7.91/1.49  git: last_make_outside_of_git: false
% 7.91/1.49  
% 7.91/1.49  ------ 
% 7.91/1.49  
% 7.91/1.49  ------ Input Options
% 7.91/1.49  
% 7.91/1.49  --out_options                           all
% 7.91/1.49  --tptp_safe_out                         true
% 7.91/1.49  --problem_path                          ""
% 7.91/1.49  --include_path                          ""
% 7.91/1.49  --clausifier                            res/vclausify_rel
% 7.91/1.49  --clausifier_options                    ""
% 7.91/1.49  --stdin                                 false
% 7.91/1.49  --stats_out                             all
% 7.91/1.49  
% 7.91/1.49  ------ General Options
% 7.91/1.49  
% 7.91/1.49  --fof                                   false
% 7.91/1.49  --time_out_real                         305.
% 7.91/1.49  --time_out_virtual                      -1.
% 7.91/1.49  --symbol_type_check                     false
% 7.91/1.49  --clausify_out                          false
% 7.91/1.49  --sig_cnt_out                           false
% 7.91/1.49  --trig_cnt_out                          false
% 7.91/1.49  --trig_cnt_out_tolerance                1.
% 7.91/1.49  --trig_cnt_out_sk_spl                   false
% 7.91/1.49  --abstr_cl_out                          false
% 7.91/1.49  
% 7.91/1.49  ------ Global Options
% 7.91/1.49  
% 7.91/1.49  --schedule                              default
% 7.91/1.49  --add_important_lit                     false
% 7.91/1.49  --prop_solver_per_cl                    1000
% 7.91/1.49  --min_unsat_core                        false
% 7.91/1.49  --soft_assumptions                      false
% 7.91/1.49  --soft_lemma_size                       3
% 7.91/1.49  --prop_impl_unit_size                   0
% 7.91/1.49  --prop_impl_unit                        []
% 7.91/1.49  --share_sel_clauses                     true
% 7.91/1.49  --reset_solvers                         false
% 7.91/1.49  --bc_imp_inh                            [conj_cone]
% 7.91/1.49  --conj_cone_tolerance                   3.
% 7.91/1.49  --extra_neg_conj                        none
% 7.91/1.49  --large_theory_mode                     true
% 7.91/1.49  --prolific_symb_bound                   200
% 7.91/1.49  --lt_threshold                          2000
% 7.91/1.49  --clause_weak_htbl                      true
% 7.91/1.49  --gc_record_bc_elim                     false
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing Options
% 7.91/1.49  
% 7.91/1.49  --preprocessing_flag                    true
% 7.91/1.49  --time_out_prep_mult                    0.1
% 7.91/1.49  --splitting_mode                        input
% 7.91/1.49  --splitting_grd                         true
% 7.91/1.49  --splitting_cvd                         false
% 7.91/1.49  --splitting_cvd_svl                     false
% 7.91/1.49  --splitting_nvd                         32
% 7.91/1.49  --sub_typing                            true
% 7.91/1.49  --prep_gs_sim                           true
% 7.91/1.49  --prep_unflatten                        true
% 7.91/1.49  --prep_res_sim                          true
% 7.91/1.49  --prep_upred                            true
% 7.91/1.49  --prep_sem_filter                       exhaustive
% 7.91/1.49  --prep_sem_filter_out                   false
% 7.91/1.49  --pred_elim                             true
% 7.91/1.49  --res_sim_input                         true
% 7.91/1.49  --eq_ax_congr_red                       true
% 7.91/1.49  --pure_diseq_elim                       true
% 7.91/1.49  --brand_transform                       false
% 7.91/1.49  --non_eq_to_eq                          false
% 7.91/1.49  --prep_def_merge                        true
% 7.91/1.49  --prep_def_merge_prop_impl              false
% 7.91/1.49  --prep_def_merge_mbd                    true
% 7.91/1.49  --prep_def_merge_tr_red                 false
% 7.91/1.49  --prep_def_merge_tr_cl                  false
% 7.91/1.49  --smt_preprocessing                     true
% 7.91/1.49  --smt_ac_axioms                         fast
% 7.91/1.49  --preprocessed_out                      false
% 7.91/1.49  --preprocessed_stats                    false
% 7.91/1.49  
% 7.91/1.49  ------ Abstraction refinement Options
% 7.91/1.49  
% 7.91/1.49  --abstr_ref                             []
% 7.91/1.49  --abstr_ref_prep                        false
% 7.91/1.49  --abstr_ref_until_sat                   false
% 7.91/1.49  --abstr_ref_sig_restrict                funpre
% 7.91/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.49  --abstr_ref_under                       []
% 7.91/1.49  
% 7.91/1.49  ------ SAT Options
% 7.91/1.49  
% 7.91/1.49  --sat_mode                              false
% 7.91/1.49  --sat_fm_restart_options                ""
% 7.91/1.49  --sat_gr_def                            false
% 7.91/1.49  --sat_epr_types                         true
% 7.91/1.49  --sat_non_cyclic_types                  false
% 7.91/1.49  --sat_finite_models                     false
% 7.91/1.49  --sat_fm_lemmas                         false
% 7.91/1.49  --sat_fm_prep                           false
% 7.91/1.49  --sat_fm_uc_incr                        true
% 7.91/1.49  --sat_out_model                         small
% 7.91/1.49  --sat_out_clauses                       false
% 7.91/1.49  
% 7.91/1.49  ------ QBF Options
% 7.91/1.49  
% 7.91/1.49  --qbf_mode                              false
% 7.91/1.49  --qbf_elim_univ                         false
% 7.91/1.49  --qbf_dom_inst                          none
% 7.91/1.49  --qbf_dom_pre_inst                      false
% 7.91/1.49  --qbf_sk_in                             false
% 7.91/1.49  --qbf_pred_elim                         true
% 7.91/1.49  --qbf_split                             512
% 7.91/1.49  
% 7.91/1.49  ------ BMC1 Options
% 7.91/1.49  
% 7.91/1.49  --bmc1_incremental                      false
% 7.91/1.49  --bmc1_axioms                           reachable_all
% 7.91/1.49  --bmc1_min_bound                        0
% 7.91/1.49  --bmc1_max_bound                        -1
% 7.91/1.49  --bmc1_max_bound_default                -1
% 7.91/1.49  --bmc1_symbol_reachability              true
% 7.91/1.49  --bmc1_property_lemmas                  false
% 7.91/1.49  --bmc1_k_induction                      false
% 7.91/1.49  --bmc1_non_equiv_states                 false
% 7.91/1.49  --bmc1_deadlock                         false
% 7.91/1.49  --bmc1_ucm                              false
% 7.91/1.49  --bmc1_add_unsat_core                   none
% 7.91/1.49  --bmc1_unsat_core_children              false
% 7.91/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.49  --bmc1_out_stat                         full
% 7.91/1.49  --bmc1_ground_init                      false
% 7.91/1.49  --bmc1_pre_inst_next_state              false
% 7.91/1.49  --bmc1_pre_inst_state                   false
% 7.91/1.49  --bmc1_pre_inst_reach_state             false
% 7.91/1.49  --bmc1_out_unsat_core                   false
% 7.91/1.49  --bmc1_aig_witness_out                  false
% 7.91/1.49  --bmc1_verbose                          false
% 7.91/1.49  --bmc1_dump_clauses_tptp                false
% 7.91/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.49  --bmc1_dump_file                        -
% 7.91/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.49  --bmc1_ucm_extend_mode                  1
% 7.91/1.49  --bmc1_ucm_init_mode                    2
% 7.91/1.49  --bmc1_ucm_cone_mode                    none
% 7.91/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.49  --bmc1_ucm_relax_model                  4
% 7.91/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.49  --bmc1_ucm_layered_model                none
% 7.91/1.49  --bmc1_ucm_max_lemma_size               10
% 7.91/1.49  
% 7.91/1.49  ------ AIG Options
% 7.91/1.49  
% 7.91/1.49  --aig_mode                              false
% 7.91/1.49  
% 7.91/1.49  ------ Instantiation Options
% 7.91/1.49  
% 7.91/1.49  --instantiation_flag                    true
% 7.91/1.49  --inst_sos_flag                         true
% 7.91/1.49  --inst_sos_phase                        true
% 7.91/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.49  --inst_lit_sel_side                     num_symb
% 7.91/1.49  --inst_solver_per_active                1400
% 7.91/1.49  --inst_solver_calls_frac                1.
% 7.91/1.49  --inst_passive_queue_type               priority_queues
% 7.91/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.49  --inst_passive_queues_freq              [25;2]
% 7.91/1.49  --inst_dismatching                      true
% 7.91/1.49  --inst_eager_unprocessed_to_passive     true
% 7.91/1.49  --inst_prop_sim_given                   true
% 7.91/1.49  --inst_prop_sim_new                     false
% 7.91/1.49  --inst_subs_new                         false
% 7.91/1.49  --inst_eq_res_simp                      false
% 7.91/1.49  --inst_subs_given                       false
% 7.91/1.49  --inst_orphan_elimination               true
% 7.91/1.49  --inst_learning_loop_flag               true
% 7.91/1.49  --inst_learning_start                   3000
% 7.91/1.49  --inst_learning_factor                  2
% 7.91/1.49  --inst_start_prop_sim_after_learn       3
% 7.91/1.49  --inst_sel_renew                        solver
% 7.91/1.49  --inst_lit_activity_flag                true
% 7.91/1.49  --inst_restr_to_given                   false
% 7.91/1.49  --inst_activity_threshold               500
% 7.91/1.49  --inst_out_proof                        true
% 7.91/1.49  
% 7.91/1.49  ------ Resolution Options
% 7.91/1.49  
% 7.91/1.49  --resolution_flag                       true
% 7.91/1.49  --res_lit_sel                           adaptive
% 7.91/1.49  --res_lit_sel_side                      none
% 7.91/1.49  --res_ordering                          kbo
% 7.91/1.49  --res_to_prop_solver                    active
% 7.91/1.49  --res_prop_simpl_new                    false
% 7.91/1.49  --res_prop_simpl_given                  true
% 7.91/1.49  --res_passive_queue_type                priority_queues
% 7.91/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.49  --res_passive_queues_freq               [15;5]
% 7.91/1.49  --res_forward_subs                      full
% 7.91/1.49  --res_backward_subs                     full
% 7.91/1.49  --res_forward_subs_resolution           true
% 7.91/1.49  --res_backward_subs_resolution          true
% 7.91/1.49  --res_orphan_elimination                true
% 7.91/1.49  --res_time_limit                        2.
% 7.91/1.49  --res_out_proof                         true
% 7.91/1.49  
% 7.91/1.49  ------ Superposition Options
% 7.91/1.49  
% 7.91/1.49  --superposition_flag                    true
% 7.91/1.49  --sup_passive_queue_type                priority_queues
% 7.91/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.49  --demod_completeness_check              fast
% 7.91/1.49  --demod_use_ground                      true
% 7.91/1.49  --sup_to_prop_solver                    passive
% 7.91/1.49  --sup_prop_simpl_new                    true
% 7.91/1.49  --sup_prop_simpl_given                  true
% 7.91/1.49  --sup_fun_splitting                     true
% 7.91/1.49  --sup_smt_interval                      50000
% 7.91/1.49  
% 7.91/1.49  ------ Superposition Simplification Setup
% 7.91/1.49  
% 7.91/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.49  --sup_immed_triv                        [TrivRules]
% 7.91/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.49  --sup_immed_bw_main                     []
% 7.91/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.49  --sup_input_bw                          []
% 7.91/1.49  
% 7.91/1.49  ------ Combination Options
% 7.91/1.49  
% 7.91/1.49  --comb_res_mult                         3
% 7.91/1.49  --comb_sup_mult                         2
% 7.91/1.49  --comb_inst_mult                        10
% 7.91/1.49  
% 7.91/1.49  ------ Debug Options
% 7.91/1.49  
% 7.91/1.49  --dbg_backtrace                         false
% 7.91/1.49  --dbg_dump_prop_clauses                 false
% 7.91/1.49  --dbg_dump_prop_clauses_file            -
% 7.91/1.49  --dbg_out_stat                          false
% 7.91/1.49  ------ Parsing...
% 7.91/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.91/1.49  ------ Proving...
% 7.91/1.49  ------ Problem Properties 
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  clauses                                 34
% 7.91/1.49  conjectures                             13
% 7.91/1.49  EPR                                     9
% 7.91/1.49  Horn                                    28
% 7.91/1.49  unary                                   17
% 7.91/1.49  binary                                  5
% 7.91/1.49  lits                                    129
% 7.91/1.49  lits eq                                 20
% 7.91/1.49  fd_pure                                 0
% 7.91/1.49  fd_pseudo                               0
% 7.91/1.49  fd_cond                                 0
% 7.91/1.49  fd_pseudo_cond                          0
% 7.91/1.49  AC symbols                              0
% 7.91/1.49  
% 7.91/1.49  ------ Schedule dynamic 5 is on 
% 7.91/1.49  
% 7.91/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  ------ 
% 7.91/1.49  Current options:
% 7.91/1.49  ------ 
% 7.91/1.49  
% 7.91/1.49  ------ Input Options
% 7.91/1.49  
% 7.91/1.49  --out_options                           all
% 7.91/1.49  --tptp_safe_out                         true
% 7.91/1.49  --problem_path                          ""
% 7.91/1.49  --include_path                          ""
% 7.91/1.49  --clausifier                            res/vclausify_rel
% 7.91/1.49  --clausifier_options                    ""
% 7.91/1.49  --stdin                                 false
% 7.91/1.49  --stats_out                             all
% 7.91/1.49  
% 7.91/1.49  ------ General Options
% 7.91/1.49  
% 7.91/1.49  --fof                                   false
% 7.91/1.49  --time_out_real                         305.
% 7.91/1.49  --time_out_virtual                      -1.
% 7.91/1.49  --symbol_type_check                     false
% 7.91/1.49  --clausify_out                          false
% 7.91/1.49  --sig_cnt_out                           false
% 7.91/1.49  --trig_cnt_out                          false
% 7.91/1.49  --trig_cnt_out_tolerance                1.
% 7.91/1.49  --trig_cnt_out_sk_spl                   false
% 7.91/1.49  --abstr_cl_out                          false
% 7.91/1.49  
% 7.91/1.49  ------ Global Options
% 7.91/1.49  
% 7.91/1.49  --schedule                              default
% 7.91/1.49  --add_important_lit                     false
% 7.91/1.49  --prop_solver_per_cl                    1000
% 7.91/1.49  --min_unsat_core                        false
% 7.91/1.49  --soft_assumptions                      false
% 7.91/1.49  --soft_lemma_size                       3
% 7.91/1.49  --prop_impl_unit_size                   0
% 7.91/1.49  --prop_impl_unit                        []
% 7.91/1.49  --share_sel_clauses                     true
% 7.91/1.49  --reset_solvers                         false
% 7.91/1.49  --bc_imp_inh                            [conj_cone]
% 7.91/1.49  --conj_cone_tolerance                   3.
% 7.91/1.49  --extra_neg_conj                        none
% 7.91/1.49  --large_theory_mode                     true
% 7.91/1.49  --prolific_symb_bound                   200
% 7.91/1.49  --lt_threshold                          2000
% 7.91/1.49  --clause_weak_htbl                      true
% 7.91/1.49  --gc_record_bc_elim                     false
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing Options
% 7.91/1.49  
% 7.91/1.49  --preprocessing_flag                    true
% 7.91/1.49  --time_out_prep_mult                    0.1
% 7.91/1.49  --splitting_mode                        input
% 7.91/1.49  --splitting_grd                         true
% 7.91/1.49  --splitting_cvd                         false
% 7.91/1.49  --splitting_cvd_svl                     false
% 7.91/1.49  --splitting_nvd                         32
% 7.91/1.49  --sub_typing                            true
% 7.91/1.49  --prep_gs_sim                           true
% 7.91/1.49  --prep_unflatten                        true
% 7.91/1.49  --prep_res_sim                          true
% 7.91/1.49  --prep_upred                            true
% 7.91/1.49  --prep_sem_filter                       exhaustive
% 7.91/1.49  --prep_sem_filter_out                   false
% 7.91/1.49  --pred_elim                             true
% 7.91/1.49  --res_sim_input                         true
% 7.91/1.49  --eq_ax_congr_red                       true
% 7.91/1.49  --pure_diseq_elim                       true
% 7.91/1.49  --brand_transform                       false
% 7.91/1.49  --non_eq_to_eq                          false
% 7.91/1.49  --prep_def_merge                        true
% 7.91/1.49  --prep_def_merge_prop_impl              false
% 7.91/1.49  --prep_def_merge_mbd                    true
% 7.91/1.49  --prep_def_merge_tr_red                 false
% 7.91/1.49  --prep_def_merge_tr_cl                  false
% 7.91/1.49  --smt_preprocessing                     true
% 7.91/1.49  --smt_ac_axioms                         fast
% 7.91/1.49  --preprocessed_out                      false
% 7.91/1.49  --preprocessed_stats                    false
% 7.91/1.49  
% 7.91/1.49  ------ Abstraction refinement Options
% 7.91/1.49  
% 7.91/1.49  --abstr_ref                             []
% 7.91/1.49  --abstr_ref_prep                        false
% 7.91/1.49  --abstr_ref_until_sat                   false
% 7.91/1.49  --abstr_ref_sig_restrict                funpre
% 7.91/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.91/1.49  --abstr_ref_under                       []
% 7.91/1.49  
% 7.91/1.49  ------ SAT Options
% 7.91/1.49  
% 7.91/1.49  --sat_mode                              false
% 7.91/1.49  --sat_fm_restart_options                ""
% 7.91/1.49  --sat_gr_def                            false
% 7.91/1.49  --sat_epr_types                         true
% 7.91/1.49  --sat_non_cyclic_types                  false
% 7.91/1.49  --sat_finite_models                     false
% 7.91/1.49  --sat_fm_lemmas                         false
% 7.91/1.49  --sat_fm_prep                           false
% 7.91/1.49  --sat_fm_uc_incr                        true
% 7.91/1.49  --sat_out_model                         small
% 7.91/1.49  --sat_out_clauses                       false
% 7.91/1.49  
% 7.91/1.49  ------ QBF Options
% 7.91/1.49  
% 7.91/1.49  --qbf_mode                              false
% 7.91/1.49  --qbf_elim_univ                         false
% 7.91/1.49  --qbf_dom_inst                          none
% 7.91/1.49  --qbf_dom_pre_inst                      false
% 7.91/1.49  --qbf_sk_in                             false
% 7.91/1.49  --qbf_pred_elim                         true
% 7.91/1.49  --qbf_split                             512
% 7.91/1.49  
% 7.91/1.49  ------ BMC1 Options
% 7.91/1.49  
% 7.91/1.49  --bmc1_incremental                      false
% 7.91/1.49  --bmc1_axioms                           reachable_all
% 7.91/1.49  --bmc1_min_bound                        0
% 7.91/1.49  --bmc1_max_bound                        -1
% 7.91/1.49  --bmc1_max_bound_default                -1
% 7.91/1.49  --bmc1_symbol_reachability              true
% 7.91/1.49  --bmc1_property_lemmas                  false
% 7.91/1.49  --bmc1_k_induction                      false
% 7.91/1.49  --bmc1_non_equiv_states                 false
% 7.91/1.49  --bmc1_deadlock                         false
% 7.91/1.49  --bmc1_ucm                              false
% 7.91/1.49  --bmc1_add_unsat_core                   none
% 7.91/1.49  --bmc1_unsat_core_children              false
% 7.91/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.91/1.49  --bmc1_out_stat                         full
% 7.91/1.49  --bmc1_ground_init                      false
% 7.91/1.49  --bmc1_pre_inst_next_state              false
% 7.91/1.49  --bmc1_pre_inst_state                   false
% 7.91/1.49  --bmc1_pre_inst_reach_state             false
% 7.91/1.49  --bmc1_out_unsat_core                   false
% 7.91/1.49  --bmc1_aig_witness_out                  false
% 7.91/1.49  --bmc1_verbose                          false
% 7.91/1.49  --bmc1_dump_clauses_tptp                false
% 7.91/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.91/1.49  --bmc1_dump_file                        -
% 7.91/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.91/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.91/1.49  --bmc1_ucm_extend_mode                  1
% 7.91/1.49  --bmc1_ucm_init_mode                    2
% 7.91/1.49  --bmc1_ucm_cone_mode                    none
% 7.91/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.91/1.49  --bmc1_ucm_relax_model                  4
% 7.91/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.91/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.91/1.49  --bmc1_ucm_layered_model                none
% 7.91/1.49  --bmc1_ucm_max_lemma_size               10
% 7.91/1.49  
% 7.91/1.49  ------ AIG Options
% 7.91/1.49  
% 7.91/1.49  --aig_mode                              false
% 7.91/1.49  
% 7.91/1.49  ------ Instantiation Options
% 7.91/1.49  
% 7.91/1.49  --instantiation_flag                    true
% 7.91/1.49  --inst_sos_flag                         true
% 7.91/1.49  --inst_sos_phase                        true
% 7.91/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.91/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.91/1.49  --inst_lit_sel_side                     none
% 7.91/1.49  --inst_solver_per_active                1400
% 7.91/1.49  --inst_solver_calls_frac                1.
% 7.91/1.49  --inst_passive_queue_type               priority_queues
% 7.91/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.91/1.49  --inst_passive_queues_freq              [25;2]
% 7.91/1.49  --inst_dismatching                      true
% 7.91/1.49  --inst_eager_unprocessed_to_passive     true
% 7.91/1.49  --inst_prop_sim_given                   true
% 7.91/1.49  --inst_prop_sim_new                     false
% 7.91/1.49  --inst_subs_new                         false
% 7.91/1.49  --inst_eq_res_simp                      false
% 7.91/1.49  --inst_subs_given                       false
% 7.91/1.49  --inst_orphan_elimination               true
% 7.91/1.49  --inst_learning_loop_flag               true
% 7.91/1.49  --inst_learning_start                   3000
% 7.91/1.49  --inst_learning_factor                  2
% 7.91/1.49  --inst_start_prop_sim_after_learn       3
% 7.91/1.49  --inst_sel_renew                        solver
% 7.91/1.49  --inst_lit_activity_flag                true
% 7.91/1.49  --inst_restr_to_given                   false
% 7.91/1.49  --inst_activity_threshold               500
% 7.91/1.49  --inst_out_proof                        true
% 7.91/1.49  
% 7.91/1.49  ------ Resolution Options
% 7.91/1.49  
% 7.91/1.49  --resolution_flag                       false
% 7.91/1.49  --res_lit_sel                           adaptive
% 7.91/1.49  --res_lit_sel_side                      none
% 7.91/1.49  --res_ordering                          kbo
% 7.91/1.49  --res_to_prop_solver                    active
% 7.91/1.49  --res_prop_simpl_new                    false
% 7.91/1.49  --res_prop_simpl_given                  true
% 7.91/1.49  --res_passive_queue_type                priority_queues
% 7.91/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.91/1.49  --res_passive_queues_freq               [15;5]
% 7.91/1.49  --res_forward_subs                      full
% 7.91/1.49  --res_backward_subs                     full
% 7.91/1.49  --res_forward_subs_resolution           true
% 7.91/1.49  --res_backward_subs_resolution          true
% 7.91/1.49  --res_orphan_elimination                true
% 7.91/1.49  --res_time_limit                        2.
% 7.91/1.49  --res_out_proof                         true
% 7.91/1.49  
% 7.91/1.49  ------ Superposition Options
% 7.91/1.49  
% 7.91/1.49  --superposition_flag                    true
% 7.91/1.49  --sup_passive_queue_type                priority_queues
% 7.91/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.91/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.91/1.49  --demod_completeness_check              fast
% 7.91/1.49  --demod_use_ground                      true
% 7.91/1.49  --sup_to_prop_solver                    passive
% 7.91/1.49  --sup_prop_simpl_new                    true
% 7.91/1.49  --sup_prop_simpl_given                  true
% 7.91/1.49  --sup_fun_splitting                     true
% 7.91/1.49  --sup_smt_interval                      50000
% 7.91/1.49  
% 7.91/1.49  ------ Superposition Simplification Setup
% 7.91/1.49  
% 7.91/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.91/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.91/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.91/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.91/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.91/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.91/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.91/1.49  --sup_immed_triv                        [TrivRules]
% 7.91/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.49  --sup_immed_bw_main                     []
% 7.91/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.91/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.91/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.91/1.49  --sup_input_bw                          []
% 7.91/1.49  
% 7.91/1.49  ------ Combination Options
% 7.91/1.49  
% 7.91/1.49  --comb_res_mult                         3
% 7.91/1.49  --comb_sup_mult                         2
% 7.91/1.49  --comb_inst_mult                        10
% 7.91/1.49  
% 7.91/1.49  ------ Debug Options
% 7.91/1.49  
% 7.91/1.49  --dbg_backtrace                         false
% 7.91/1.49  --dbg_dump_prop_clauses                 false
% 7.91/1.49  --dbg_dump_prop_clauses_file            -
% 7.91/1.49  --dbg_out_stat                          false
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  ------ Proving...
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  % SZS status Theorem for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  fof(f16,conjecture,(
% 7.91/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f17,negated_conjecture,(
% 7.91/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.91/1.49    inference(negated_conjecture,[],[f16])).
% 7.91/1.49  
% 7.91/1.49  fof(f34,plain,(
% 7.91/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.91/1.49    inference(ennf_transformation,[],[f17])).
% 7.91/1.49  
% 7.91/1.49  fof(f35,plain,(
% 7.91/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.91/1.49    inference(flattening,[],[f34])).
% 7.91/1.49  
% 7.91/1.49  fof(f46,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f45,plain,(
% 7.91/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f44,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f43,plain,(
% 7.91/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f42,plain,(
% 7.91/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f41,plain,(
% 7.91/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.91/1.49    introduced(choice_axiom,[])).
% 7.91/1.49  
% 7.91/1.49  fof(f47,plain,(
% 7.91/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.91/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f46,f45,f44,f43,f42,f41])).
% 7.91/1.49  
% 7.91/1.49  fof(f75,plain,(
% 7.91/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f2,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f19,plain,(
% 7.91/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.91/1.49    inference(ennf_transformation,[],[f2])).
% 7.91/1.49  
% 7.91/1.49  fof(f50,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f19])).
% 7.91/1.49  
% 7.91/1.49  fof(f79,plain,(
% 7.91/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f13,axiom,(
% 7.91/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f28,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.91/1.49    inference(ennf_transformation,[],[f13])).
% 7.91/1.49  
% 7.91/1.49  fof(f29,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.91/1.49    inference(flattening,[],[f28])).
% 7.91/1.49  
% 7.91/1.49  fof(f63,plain,(
% 7.91/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f29])).
% 7.91/1.49  
% 7.91/1.49  fof(f77,plain,(
% 7.91/1.49    v1_funct_1(sK4)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f82,plain,(
% 7.91/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f80,plain,(
% 7.91/1.49    v1_funct_1(sK5)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f14,axiom,(
% 7.91/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f30,plain,(
% 7.91/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.91/1.49    inference(ennf_transformation,[],[f14])).
% 7.91/1.49  
% 7.91/1.49  fof(f31,plain,(
% 7.91/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.91/1.49    inference(flattening,[],[f30])).
% 7.91/1.49  
% 7.91/1.49  fof(f39,plain,(
% 7.91/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.91/1.49    inference(nnf_transformation,[],[f31])).
% 7.91/1.49  
% 7.91/1.49  fof(f40,plain,(
% 7.91/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.91/1.49    inference(flattening,[],[f39])).
% 7.91/1.49  
% 7.91/1.49  fof(f65,plain,(
% 7.91/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f40])).
% 7.91/1.49  
% 7.91/1.49  fof(f86,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(equality_resolution,[],[f65])).
% 7.91/1.49  
% 7.91/1.49  fof(f15,axiom,(
% 7.91/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f32,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.91/1.49    inference(ennf_transformation,[],[f15])).
% 7.91/1.49  
% 7.91/1.49  fof(f33,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.91/1.49    inference(flattening,[],[f32])).
% 7.91/1.49  
% 7.91/1.49  fof(f67,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f33])).
% 7.91/1.49  
% 7.91/1.49  fof(f68,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f33])).
% 7.91/1.49  
% 7.91/1.49  fof(f69,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f33])).
% 7.91/1.49  
% 7.91/1.49  fof(f71,plain,(
% 7.91/1.49    ~v1_xboole_0(sK1)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f74,plain,(
% 7.91/1.49    ~v1_xboole_0(sK3)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f81,plain,(
% 7.91/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f72,plain,(
% 7.91/1.49    ~v1_xboole_0(sK2)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f78,plain,(
% 7.91/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f4,axiom,(
% 7.91/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f20,plain,(
% 7.91/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.91/1.49    inference(ennf_transformation,[],[f4])).
% 7.91/1.49  
% 7.91/1.49  fof(f52,plain,(
% 7.91/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f20])).
% 7.91/1.49  
% 7.91/1.49  fof(f9,axiom,(
% 7.91/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f22,plain,(
% 7.91/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.91/1.49    inference(ennf_transformation,[],[f9])).
% 7.91/1.49  
% 7.91/1.49  fof(f23,plain,(
% 7.91/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.91/1.49    inference(flattening,[],[f22])).
% 7.91/1.49  
% 7.91/1.49  fof(f38,plain,(
% 7.91/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.91/1.49    inference(nnf_transformation,[],[f23])).
% 7.91/1.49  
% 7.91/1.49  fof(f58,plain,(
% 7.91/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f38])).
% 7.91/1.49  
% 7.91/1.49  fof(f76,plain,(
% 7.91/1.49    r1_subset_1(sK2,sK3)),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f1,axiom,(
% 7.91/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f36,plain,(
% 7.91/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.91/1.49    inference(nnf_transformation,[],[f1])).
% 7.91/1.49  
% 7.91/1.49  fof(f48,plain,(
% 7.91/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f36])).
% 7.91/1.49  
% 7.91/1.49  fof(f6,axiom,(
% 7.91/1.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f53,plain,(
% 7.91/1.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f6])).
% 7.91/1.49  
% 7.91/1.49  fof(f7,axiom,(
% 7.91/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f21,plain,(
% 7.91/1.49    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.91/1.49    inference(ennf_transformation,[],[f7])).
% 7.91/1.49  
% 7.91/1.49  fof(f37,plain,(
% 7.91/1.49    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.91/1.49    inference(nnf_transformation,[],[f21])).
% 7.91/1.49  
% 7.91/1.49  fof(f54,plain,(
% 7.91/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f37])).
% 7.91/1.49  
% 7.91/1.49  fof(f8,axiom,(
% 7.91/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f56,plain,(
% 7.91/1.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.91/1.49    inference(cnf_transformation,[],[f8])).
% 7.91/1.49  
% 7.91/1.49  fof(f3,axiom,(
% 7.91/1.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f51,plain,(
% 7.91/1.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f3])).
% 7.91/1.49  
% 7.91/1.49  fof(f10,axiom,(
% 7.91/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f24,plain,(
% 7.91/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.49    inference(ennf_transformation,[],[f10])).
% 7.91/1.49  
% 7.91/1.49  fof(f60,plain,(
% 7.91/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f24])).
% 7.91/1.49  
% 7.91/1.49  fof(f12,axiom,(
% 7.91/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f26,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3] : ((k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) | ~r1_xboole_0(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.91/1.49    inference(ennf_transformation,[],[f12])).
% 7.91/1.49  
% 7.91/1.49  fof(f27,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3] : (k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 7.91/1.49    inference(flattening,[],[f26])).
% 7.91/1.49  
% 7.91/1.49  fof(f62,plain,(
% 7.91/1.49    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f27])).
% 7.91/1.49  
% 7.91/1.49  fof(f11,axiom,(
% 7.91/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 7.91/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.91/1.49  
% 7.91/1.49  fof(f25,plain,(
% 7.91/1.49    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.91/1.49    inference(ennf_transformation,[],[f11])).
% 7.91/1.49  
% 7.91/1.49  fof(f61,plain,(
% 7.91/1.49    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.91/1.49    inference(cnf_transformation,[],[f25])).
% 7.91/1.49  
% 7.91/1.49  fof(f64,plain,(
% 7.91/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(cnf_transformation,[],[f40])).
% 7.91/1.49  
% 7.91/1.49  fof(f87,plain,(
% 7.91/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.91/1.49    inference(equality_resolution,[],[f64])).
% 7.91/1.49  
% 7.91/1.49  fof(f83,plain,(
% 7.91/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  fof(f73,plain,(
% 7.91/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.91/1.49    inference(cnf_transformation,[],[f47])).
% 7.91/1.49  
% 7.91/1.49  cnf(c_30,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1020,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_30]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1811,plain,
% 7.91/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1043,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.91/1.49      | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1792,plain,
% 7.91/1.49      ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
% 7.91/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1043]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2565,plain,
% 7.91/1.49      ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1811,c_1792]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_26,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1023,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_26]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1808,plain,
% 7.91/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_15,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.91/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1032,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.91/1.49      | ~ v1_funct_1(X0_54)
% 7.91/1.49      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1800,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.91/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.91/1.49      | v1_funct_1(X2_54) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1032]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3759,plain,
% 7.91/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 7.91/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1808,c_1800]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_28,negated_conjecture,
% 7.91/1.49      ( v1_funct_1(sK4) ),
% 7.91/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_43,plain,
% 7.91/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3835,plain,
% 7.91/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_3759,c_43]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_23,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.91/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1026,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1805,plain,
% 7.91/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3758,plain,
% 7.91/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 7.91/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1805,c_1800]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_25,negated_conjecture,
% 7.91/1.49      ( v1_funct_1(sK5) ),
% 7.91/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_46,plain,
% 7.91/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3789,plain,
% 7.91/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_3758,c_46]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_17,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_21,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_20,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_19,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_191,plain,
% 7.91/1.49      ( ~ v1_funct_1(X3)
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_17,c_21,c_20,c_19]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_192,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_191]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1013,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.91/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.91/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.91/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.91/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.91/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.91/1.49      | ~ v1_funct_1(X0_54)
% 7.91/1.49      | ~ v1_funct_1(X3_54)
% 7.91/1.49      | v1_xboole_0(X1_54)
% 7.91/1.49      | v1_xboole_0(X2_54)
% 7.91/1.49      | v1_xboole_0(X4_54)
% 7.91/1.49      | v1_xboole_0(X5_54)
% 7.91/1.49      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_192]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1818,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.91/1.49      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.91/1.49      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.91/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.91/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.91/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.91/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.91/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_6066,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.91/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.91/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.91/1.49      | v1_funct_1(sK5) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.91/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3789,c_1818]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_34,negated_conjecture,
% 7.91/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_37,plain,
% 7.91/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_31,negated_conjecture,
% 7.91/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.91/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_40,plain,
% 7.91/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_24,negated_conjecture,
% 7.91/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_47,plain,
% 7.91/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_48,plain,
% 7.91/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11657,plain,
% 7.91/1.49      ( v1_funct_1(X1_54) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.91/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.91/1.49      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X2_54) = iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_6066,c_37,c_40,c_46,c_47,c_48]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11658,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.91/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.91/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_11657]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11664,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.91/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.91/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | v1_funct_1(sK4) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3835,c_11658]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_33,negated_conjecture,
% 7.91/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.91/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_38,plain,
% 7.91/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_27,negated_conjecture,
% 7.91/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_44,plain,
% 7.91/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_45,plain,
% 7.91/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.91/1.49      | ~ v1_xboole_0(X1)
% 7.91/1.49      | v1_xboole_0(X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1041,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.91/1.49      | ~ v1_xboole_0(X1_54)
% 7.91/1.49      | v1_xboole_0(X0_54) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1972,plain,
% 7.91/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_54))
% 7.91/1.49      | ~ v1_xboole_0(X0_54)
% 7.91/1.49      | v1_xboole_0(sK2) ),
% 7.91/1.49      inference(instantiation,[status(thm)],[c_1041]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1973,plain,
% 7.91/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) != iProver_top
% 7.91/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1972]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12914,plain,
% 7.91/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_11664,c_38,c_43,c_44,c_45,c_1973]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12915,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_12914]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12920,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_2565,c_12915]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_11,plain,
% 7.91/1.49      ( ~ r1_subset_1(X0,X1)
% 7.91/1.49      | r1_xboole_0(X0,X1)
% 7.91/1.49      | v1_xboole_0(X0)
% 7.91/1.49      | v1_xboole_0(X1) ),
% 7.91/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_29,negated_conjecture,
% 7.91/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.91/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_472,plain,
% 7.91/1.49      ( r1_xboole_0(X0,X1)
% 7.91/1.49      | v1_xboole_0(X0)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | sK3 != X1
% 7.91/1.49      | sK2 != X0 ),
% 7.91/1.49      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_473,plain,
% 7.91/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.91/1.49      inference(unflattening,[status(thm)],[c_472]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_475,plain,
% 7.91/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_473,c_33,c_31]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1012,plain,
% 7.91/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_475]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1819,plain,
% 7.91/1.49      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1,plain,
% 7.91/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1044,plain,
% 7.91/1.49      ( ~ r1_xboole_0(X0_54,X1_54)
% 7.91/1.49      | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1791,plain,
% 7.91/1.49      ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
% 7.91/1.49      | r1_xboole_0(X0_54,X1_54) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1044]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2937,plain,
% 7.91/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1819,c_1791]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5,plain,
% 7.91/1.49      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1040,plain,
% 7.91/1.49      ( k9_relat_1(k1_xboole_0,X0_54) = k1_xboole_0 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_7,plain,
% 7.91/1.49      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.91/1.49      | ~ v1_relat_1(X0)
% 7.91/1.49      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1038,plain,
% 7.91/1.49      ( r1_xboole_0(k1_relat_1(X0_54),X1_54)
% 7.91/1.49      | ~ v1_relat_1(X0_54)
% 7.91/1.49      | k9_relat_1(X0_54,X1_54) != k1_xboole_0 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1796,plain,
% 7.91/1.49      ( k9_relat_1(X0_54,X1_54) != k1_xboole_0
% 7.91/1.49      | r1_xboole_0(k1_relat_1(X0_54),X1_54) = iProver_top
% 7.91/1.49      | v1_relat_1(X0_54) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1038]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3681,plain,
% 7.91/1.49      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0_54) = iProver_top
% 7.91/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1040,c_1796]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_9,plain,
% 7.91/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1036,plain,
% 7.91/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3682,plain,
% 7.91/1.49      ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top
% 7.91/1.49      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.91/1.49      inference(light_normalisation,[status(thm)],[c_3681,c_1036]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3,plain,
% 7.91/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1042,plain,
% 7.91/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1793,plain,
% 7.91/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_54)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1042]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | v1_relat_1(X0) ),
% 7.91/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1035,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.91/1.49      | v1_relat_1(X0_54) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1797,plain,
% 7.91/1.49      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.91/1.49      | v1_relat_1(X0_54) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3445,plain,
% 7.91/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1793,c_1797]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3703,plain,
% 7.91/1.49      ( r1_xboole_0(k1_xboole_0,X0_54) = iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_3682,c_3445]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_14,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ r1_xboole_0(X3,X1)
% 7.91/1.49      | k5_relset_1(X1,X2,X0,X3) = k1_xboole_0 ),
% 7.91/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1033,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.91/1.49      | ~ r1_xboole_0(X3_54,X1_54)
% 7.91/1.49      | k5_relset_1(X1_54,X2_54,X0_54,X3_54) = k1_xboole_0 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1799,plain,
% 7.91/1.49      ( k5_relset_1(X0_54,X1_54,X2_54,X3_54) = k1_xboole_0
% 7.91/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.91/1.49      | r1_xboole_0(X3_54,X0_54) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3712,plain,
% 7.91/1.49      ( k5_relset_1(sK3,sK1,sK5,X0_54) = k1_xboole_0
% 7.91/1.49      | r1_xboole_0(X0_54,sK3) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1805,c_1799]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_13,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.91/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1034,plain,
% 7.91/1.49      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.91/1.49      | k5_relset_1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1798,plain,
% 7.91/1.49      ( k5_relset_1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.91/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1034]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3674,plain,
% 7.91/1.49      ( k5_relset_1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1805,c_1798]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3717,plain,
% 7.91/1.49      ( k7_relat_1(sK5,X0_54) = k1_xboole_0
% 7.91/1.49      | r1_xboole_0(X0_54,sK3) != iProver_top ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_3712,c_3674]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3894,plain,
% 7.91/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3703,c_3717]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12921,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(light_normalisation,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_12920,c_2937,c_3894]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12922,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_12921,c_2565]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3713,plain,
% 7.91/1.49      ( k5_relset_1(sK2,sK1,sK4,X0_54) = k1_xboole_0
% 7.91/1.49      | r1_xboole_0(X0_54,sK2) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1808,c_1799]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3675,plain,
% 7.91/1.49      ( k5_relset_1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_1808,c_1798]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3716,plain,
% 7.91/1.49      ( k7_relat_1(sK4,X0_54) = k1_xboole_0
% 7.91/1.49      | r1_xboole_0(X0_54,sK2) != iProver_top ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_3713,c_3675]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3891,plain,
% 7.91/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3703,c_3716]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12923,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | k1_xboole_0 != k1_xboole_0
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(light_normalisation,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_12922,c_2937,c_3891]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_12924,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_12923]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_18,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.91/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_184,plain,
% 7.91/1.49      ( ~ v1_funct_1(X3)
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_18,c_21,c_20,c_19]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_185,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.91/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.91/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.91/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.91/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.91/1.49      | ~ v1_funct_1(X0)
% 7.91/1.49      | ~ v1_funct_1(X3)
% 7.91/1.49      | v1_xboole_0(X1)
% 7.91/1.49      | v1_xboole_0(X2)
% 7.91/1.49      | v1_xboole_0(X4)
% 7.91/1.49      | v1_xboole_0(X5)
% 7.91/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_184]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1014,plain,
% 7.91/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.91/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.91/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.91/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.91/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.91/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.91/1.49      | ~ v1_funct_1(X0_54)
% 7.91/1.49      | ~ v1_funct_1(X3_54)
% 7.91/1.49      | v1_xboole_0(X1_54)
% 7.91/1.49      | v1_xboole_0(X2_54)
% 7.91/1.49      | v1_xboole_0(X4_54)
% 7.91/1.49      | v1_xboole_0(X5_54)
% 7.91/1.49      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_185]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1817,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.91/1.49      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.91/1.49      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.91/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.91/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.91/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.91/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.91/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_1014]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4391,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.91/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.91/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.91/1.49      | v1_funct_1(sK5) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.91/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3789,c_1817]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5761,plain,
% 7.91/1.49      ( v1_funct_1(X1_54) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.91/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.91/1.49      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X2_54) = iProver_top ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_4391,c_37,c_40,c_46,c_47,c_48]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5762,plain,
% 7.91/1.49      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.91/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.91/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.91/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.91/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_5761]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5768,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.91/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.91/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | v1_funct_1(sK4) != iProver_top
% 7.91/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.91/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_3835,c_5762]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5883,plain,
% 7.91/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.91/1.49      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.91/1.49      inference(global_propositional_subsumption,
% 7.91/1.49                [status(thm)],
% 7.91/1.49                [c_5768,c_38,c_43,c_44,c_45,c_1973]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5884,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.91/1.49      inference(renaming,[status(thm)],[c_5883]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5889,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(superposition,[status(thm)],[c_2565,c_5884]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5890,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(light_normalisation,[status(thm)],[c_5889,c_2937,c_3894]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5891,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_5890,c_2565]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5892,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | k1_xboole_0 != k1_xboole_0
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(light_normalisation,[status(thm)],[c_5891,c_2937,c_3891]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_5893,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.91/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.91/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_5892]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_22,negated_conjecture,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_1027,negated_conjecture,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.91/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_2753,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_2565,c_1027]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3623,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_2937,c_2753]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_3838,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_3623,c_3789,c_3835]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4254,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 7.91/1.49      inference(demodulation,[status(thm)],[c_3891,c_3838]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4255,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.91/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.91/1.49      inference(light_normalisation,[status(thm)],[c_4254,c_3894]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_4256,plain,
% 7.91/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.91/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.91/1.49      inference(equality_resolution_simp,[status(thm)],[c_4255]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_41,plain,
% 7.91/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_32,negated_conjecture,
% 7.91/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.91/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(c_39,plain,
% 7.91/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.91/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.91/1.49  
% 7.91/1.49  cnf(contradiction,plain,
% 7.91/1.49      ( $false ),
% 7.91/1.49      inference(minisat,[status(thm)],[c_12924,c_5893,c_4256,c_41,c_39]) ).
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.91/1.49  
% 7.91/1.49  ------                               Statistics
% 7.91/1.49  
% 7.91/1.49  ------ General
% 7.91/1.49  
% 7.91/1.49  abstr_ref_over_cycles:                  0
% 7.91/1.49  abstr_ref_under_cycles:                 0
% 7.91/1.49  gc_basic_clause_elim:                   0
% 7.91/1.49  forced_gc_time:                         0
% 7.91/1.49  parsing_time:                           0.018
% 7.91/1.49  unif_index_cands_time:                  0.
% 7.91/1.49  unif_index_add_time:                    0.
% 7.91/1.49  orderings_time:                         0.
% 7.91/1.49  out_proof_time:                         0.015
% 7.91/1.49  total_time:                             0.958
% 7.91/1.49  num_of_symbols:                         59
% 7.91/1.49  num_of_terms:                           43086
% 7.91/1.49  
% 7.91/1.49  ------ Preprocessing
% 7.91/1.49  
% 7.91/1.49  num_of_splits:                          0
% 7.91/1.49  num_of_split_atoms:                     0
% 7.91/1.49  num_of_reused_defs:                     0
% 7.91/1.49  num_eq_ax_congr_red:                    31
% 7.91/1.49  num_of_sem_filtered_clauses:            1
% 7.91/1.49  num_of_subtypes:                        2
% 7.91/1.49  monotx_restored_types:                  0
% 7.91/1.49  sat_num_of_epr_types:                   0
% 7.91/1.49  sat_num_of_non_cyclic_types:            0
% 7.91/1.49  sat_guarded_non_collapsed_types:        1
% 7.91/1.49  num_pure_diseq_elim:                    0
% 7.91/1.49  simp_replaced_by:                       0
% 7.91/1.49  res_preprocessed:                       173
% 7.91/1.49  prep_upred:                             0
% 7.91/1.49  prep_unflattend:                        28
% 7.91/1.49  smt_new_axioms:                         0
% 7.91/1.49  pred_elim_cands:                        6
% 7.91/1.49  pred_elim:                              1
% 7.91/1.49  pred_elim_cl:                           2
% 7.91/1.49  pred_elim_cycles:                       5
% 7.91/1.49  merged_defs:                            8
% 7.91/1.49  merged_defs_ncl:                        0
% 7.91/1.49  bin_hyper_res:                          8
% 7.91/1.49  prep_cycles:                            4
% 7.91/1.49  pred_elim_time:                         0.009
% 7.91/1.49  splitting_time:                         0.
% 7.91/1.49  sem_filter_time:                        0.
% 7.91/1.49  monotx_time:                            0.
% 7.91/1.49  subtype_inf_time:                       0.002
% 7.91/1.49  
% 7.91/1.49  ------ Problem properties
% 7.91/1.49  
% 7.91/1.49  clauses:                                34
% 7.91/1.49  conjectures:                            13
% 7.91/1.49  epr:                                    9
% 7.91/1.49  horn:                                   28
% 7.91/1.49  ground:                                 16
% 7.91/1.49  unary:                                  17
% 7.91/1.49  binary:                                 5
% 7.91/1.49  lits:                                   129
% 7.91/1.49  lits_eq:                                20
% 7.91/1.49  fd_pure:                                0
% 7.91/1.49  fd_pseudo:                              0
% 7.91/1.49  fd_cond:                                0
% 7.91/1.49  fd_pseudo_cond:                         0
% 7.91/1.49  ac_symbols:                             0
% 7.91/1.49  
% 7.91/1.49  ------ Propositional Solver
% 7.91/1.49  
% 7.91/1.49  prop_solver_calls:                      30
% 7.91/1.49  prop_fast_solver_calls:                 3404
% 7.91/1.49  smt_solver_calls:                       0
% 7.91/1.49  smt_fast_solver_calls:                  0
% 7.91/1.49  prop_num_of_clauses:                    7305
% 7.91/1.49  prop_preprocess_simplified:             14514
% 7.91/1.49  prop_fo_subsumed:                       277
% 7.91/1.49  prop_solver_time:                       0.
% 7.91/1.49  smt_solver_time:                        0.
% 7.91/1.49  smt_fast_solver_time:                   0.
% 7.91/1.49  prop_fast_solver_time:                  0.
% 7.91/1.49  prop_unsat_core_time:                   0.001
% 7.91/1.49  
% 7.91/1.49  ------ QBF
% 7.91/1.49  
% 7.91/1.49  qbf_q_res:                              0
% 7.91/1.49  qbf_num_tautologies:                    0
% 7.91/1.49  qbf_prep_cycles:                        0
% 7.91/1.49  
% 7.91/1.49  ------ BMC1
% 7.91/1.49  
% 7.91/1.49  bmc1_current_bound:                     -1
% 7.91/1.49  bmc1_last_solved_bound:                 -1
% 7.91/1.49  bmc1_unsat_core_size:                   -1
% 7.91/1.49  bmc1_unsat_core_parents_size:           -1
% 7.91/1.49  bmc1_merge_next_fun:                    0
% 7.91/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.91/1.49  
% 7.91/1.49  ------ Instantiation
% 7.91/1.49  
% 7.91/1.49  inst_num_of_clauses:                    1614
% 7.91/1.49  inst_num_in_passive:                    317
% 7.91/1.49  inst_num_in_active:                     1011
% 7.91/1.49  inst_num_in_unprocessed:                286
% 7.91/1.49  inst_num_of_loops:                      1190
% 7.91/1.49  inst_num_of_learning_restarts:          0
% 7.91/1.49  inst_num_moves_active_passive:          176
% 7.91/1.49  inst_lit_activity:                      0
% 7.91/1.49  inst_lit_activity_moves:                1
% 7.91/1.49  inst_num_tautologies:                   0
% 7.91/1.49  inst_num_prop_implied:                  0
% 7.91/1.49  inst_num_existing_simplified:           0
% 7.91/1.49  inst_num_eq_res_simplified:             0
% 7.91/1.49  inst_num_child_elim:                    0
% 7.91/1.49  inst_num_of_dismatching_blockings:      156
% 7.91/1.49  inst_num_of_non_proper_insts:           1744
% 7.91/1.49  inst_num_of_duplicates:                 0
% 7.91/1.49  inst_inst_num_from_inst_to_res:         0
% 7.91/1.49  inst_dismatching_checking_time:         0.
% 7.91/1.49  
% 7.91/1.49  ------ Resolution
% 7.91/1.49  
% 7.91/1.49  res_num_of_clauses:                     0
% 7.91/1.49  res_num_in_passive:                     0
% 7.91/1.49  res_num_in_active:                      0
% 7.91/1.49  res_num_of_loops:                       177
% 7.91/1.49  res_forward_subset_subsumed:            41
% 7.91/1.49  res_backward_subset_subsumed:           0
% 7.91/1.49  res_forward_subsumed:                   0
% 7.91/1.49  res_backward_subsumed:                  0
% 7.91/1.49  res_forward_subsumption_resolution:     0
% 7.91/1.49  res_backward_subsumption_resolution:    0
% 7.91/1.49  res_clause_to_clause_subsumption:       924
% 7.91/1.49  res_orphan_elimination:                 0
% 7.91/1.49  res_tautology_del:                      27
% 7.91/1.49  res_num_eq_res_simplified:              0
% 7.91/1.49  res_num_sel_changes:                    0
% 7.91/1.49  res_moves_from_active_to_pass:          0
% 7.91/1.49  
% 7.91/1.49  ------ Superposition
% 7.91/1.49  
% 7.91/1.49  sup_time_total:                         0.
% 7.91/1.49  sup_time_generating:                    0.
% 7.91/1.49  sup_time_sim_full:                      0.
% 7.91/1.49  sup_time_sim_immed:                     0.
% 7.91/1.49  
% 7.91/1.49  sup_num_of_clauses:                     317
% 7.91/1.49  sup_num_in_active:                      235
% 7.91/1.49  sup_num_in_passive:                     82
% 7.91/1.49  sup_num_of_loops:                       237
% 7.91/1.49  sup_fw_superposition:                   280
% 7.91/1.49  sup_bw_superposition:                   55
% 7.91/1.49  sup_immediate_simplified:               137
% 7.91/1.49  sup_given_eliminated:                   0
% 7.91/1.49  comparisons_done:                       0
% 7.91/1.49  comparisons_avoided:                    0
% 7.91/1.49  
% 7.91/1.49  ------ Simplifications
% 7.91/1.49  
% 7.91/1.49  
% 7.91/1.49  sim_fw_subset_subsumed:                 9
% 7.91/1.49  sim_bw_subset_subsumed:                 0
% 7.91/1.49  sim_fw_subsumed:                        10
% 7.91/1.49  sim_bw_subsumed:                        10
% 7.91/1.49  sim_fw_subsumption_res:                 0
% 7.91/1.49  sim_bw_subsumption_res:                 0
% 7.91/1.49  sim_tautology_del:                      0
% 7.91/1.49  sim_eq_tautology_del:                   4
% 7.91/1.49  sim_eq_res_simp:                        4
% 7.91/1.49  sim_fw_demodulated:                     69
% 7.91/1.49  sim_bw_demodulated:                     3
% 7.91/1.49  sim_light_normalised:                   46
% 7.91/1.49  sim_joinable_taut:                      0
% 7.91/1.49  sim_joinable_simp:                      0
% 7.91/1.49  sim_ac_normalised:                      0
% 7.91/1.49  sim_smt_subsumption:                    0
% 7.91/1.49  
%------------------------------------------------------------------------------
