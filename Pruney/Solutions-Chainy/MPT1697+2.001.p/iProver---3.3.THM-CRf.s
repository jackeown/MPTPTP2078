%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:21 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  333 (9116 expanded)
%              Number of clauses        :  227 (2381 expanded)
%              Number of leaves         :   28 (3066 expanded)
%              Depth                    :   37
%              Number of atoms          : 1669 (94545 expanded)
%              Number of equality atoms :  677 (21075 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

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
    inference(ennf_transformation,[],[f23])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f62,plain,(
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

fof(f61,plain,(
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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,
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

fof(f63,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f49,f62,f61,f60,f59,f58,f57])).

fof(f105,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f101,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f108,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

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
    inference(nnf_transformation,[],[f45])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f90])).

fof(f21,axiom,(
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
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f93,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f107,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f104,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,(
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
    inference(cnf_transformation,[],[f56])).

fof(f116,plain,(
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
    inference(equality_resolution,[],[f91])).

fof(f109,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1924,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_2918,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1924])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1933,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2910,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1933])).

cnf(c_5376,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_2910])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_3476,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_3761,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(instantiation,[status(thm)],[c_3476])).

cnf(c_5967,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5376,c_37,c_35,c_3761])).

cnf(c_17,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_618,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_38])).

cnf(c_619,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_621,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_619,c_42,c_40])).

cnf(c_1913,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_621])).

cnf(c_2929,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1949,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2896,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_4026,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2929,c_2896])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1921,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_2921,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1921])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1947,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2898,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1947])).

cnf(c_4032,plain,
    ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
    inference(superposition,[status(thm)],[c_2921,c_2898])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1927,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2915,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1927])).

cnf(c_5375,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_2910])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3471,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_3756,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(instantiation,[status(thm)],[c_3471])).

cnf(c_5961,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5375,c_34,c_32,c_3756])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f117])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f93])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f95])).

cnf(c_236,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_30,c_29,c_28])).

cnf(c_237,plain,
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
    inference(renaming,[status(thm)],[c_236])).

cnf(c_1915,plain,
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
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_2927,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1946,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2899,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
    | v1_xboole_0(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1946])).

cnf(c_3147,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2927,c_2899])).

cnf(c_11583,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,X0_57,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_57,X0_57,sK3))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK3),sK1,k1_tmap_1(X2_57,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5961,c_3147])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_46,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_49,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_55,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_56,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_57,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_13800,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK3),sK1,k1_tmap_1(X2_57,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,X0_57,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_57,X0_57,sK3))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11583,c_46,c_49,c_55,c_56,c_57])).

cnf(c_13801,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,X0_57,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_57,X0_57,sK3))
    | k2_partfun1(k4_subset_1(X2_57,X0_57,sK3),sK1,k1_tmap_1(X2_57,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_13800])).

cnf(c_13816,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k9_subset_1(sK0,X0_57,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(superposition,[status(thm)],[c_4032,c_13801])).

cnf(c_13825,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_57,sK3)))
    | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13816,c_4032])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_13912,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_57,sK3)))
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13825,c_50])).

cnf(c_13913,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_57,sK3)))
    | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_13912])).

cnf(c_13927,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,X0_57,k1_xboole_0)
    | v1_funct_2(X0_57,sK2,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4026,c_13913])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1934,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2909,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1934])).

cnf(c_4199,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_2909])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_23,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_573,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_19,c_23])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_23,c_19,c_18])).

cnf(c_578,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_577])).

cnf(c_631,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_20,c_578])).

cnf(c_635,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_631,c_23,c_20,c_19,c_18])).

cnf(c_636,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_635])).

cnf(c_1912,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | v1_xboole_0(X2_57)
    | k1_relat_1(X0_57) = X1_57 ),
    inference(subtyping,[status(esa)],[c_636])).

cnf(c_2930,plain,
    ( k1_relat_1(X0_57) = X1_57
    | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1912])).

cnf(c_6578,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2915,c_2930])).

cnf(c_3461,plain,
    ( ~ v1_funct_2(sK5,X0_57,X1_57)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK5) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_3750,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_3461])).

cnf(c_6599,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6578,c_43,c_34,c_33,c_32,c_3750])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1940,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2905,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1940])).

cnf(c_6612,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6599,c_2905])).

cnf(c_3349,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_3350,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3349])).

cnf(c_6727,plain,
    ( r1_xboole_0(X0_57,sK3) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6612,c_57,c_3350])).

cnf(c_6728,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6727])).

cnf(c_6735,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2929,c_6728])).

cnf(c_13,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1937,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57)
    | ~ v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2906,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1937])).

cnf(c_7540,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6735,c_2906])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1938,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_7543,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7540,c_1938])).

cnf(c_8504,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7543,c_57,c_3350])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1941,plain,
    ( ~ r1_tarski(X0_57,X1_57)
    | ~ v1_relat_1(X2_57)
    | k9_relat_1(k7_relat_1(X2_57,X1_57),X0_57) = k9_relat_1(X2_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2904,plain,
    ( k9_relat_1(k7_relat_1(X0_57,X1_57),X2_57) = k9_relat_1(X0_57,X2_57)
    | r1_tarski(X2_57,X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_8509,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8504,c_2904])).

cnf(c_8517,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4199,c_8509])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1948,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2897,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_5,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1945,plain,
    ( v1_relat_1(X0_57)
    | ~ v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2900,plain,
    ( v1_relat_1(X0_57) = iProver_top
    | v1_xboole_0(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_3927,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2897,c_2900])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1944,plain,
    ( ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2901,plain,
    ( k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_4122,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3927,c_2901])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1939,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_4123,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4122,c_1938,c_1939])).

cnf(c_8522,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8517,c_4123,c_6735])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1942,plain,
    ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2903,plain,
    ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(c_8622,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8522,c_2903])).

cnf(c_8623,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8622,c_6599])).

cnf(c_8809,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8623,c_57,c_3350])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1936,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2907,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_6611,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6599,c_2907])).

cnf(c_6718,plain,
    ( r1_xboole_0(sK3,X0_57) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6611,c_57,c_3350])).

cnf(c_6719,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_6718])).

cnf(c_8817,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8809,c_6719])).

cnf(c_13936,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
    | k2_partfun1(sK2,sK1,X0_57,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_57,sK2,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13927,c_4026,c_8817])).

cnf(c_47,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_28399,plain,
    ( v1_funct_1(X0_57) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
    | k2_partfun1(sK2,sK1,X0_57,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_57,sK2,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13936,c_47,c_48])).

cnf(c_28400,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
    | k2_partfun1(sK2,sK1,X0_57,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_57,sK2,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_28399])).

cnf(c_28410,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5967,c_28400])).

cnf(c_4200,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_2909])).

cnf(c_6579,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_2930])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3466,plain,
    ( ~ v1_funct_2(sK4,X0_57,X1_57)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK4) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_3753,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_3466])).

cnf(c_7365,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6579,c_43,c_37,c_36,c_35,c_3753])).

cnf(c_7377,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7365,c_2907])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3352,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_3353,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3352])).

cnf(c_8825,plain,
    ( r1_xboole_0(sK2,X0_57) != iProver_top
    | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7377,c_54,c_3353])).

cnf(c_8826,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_8825])).

cnf(c_8833,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2929,c_8826])).

cnf(c_8993,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8833,c_2906])).

cnf(c_8996,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8993,c_1938])).

cnf(c_9466,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8996,c_54,c_3353])).

cnf(c_9471,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_9466,c_2904])).

cnf(c_9869,plain,
    ( k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4200,c_9471])).

cnf(c_9871,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9869,c_4123,c_8833])).

cnf(c_10189,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9871,c_2903])).

cnf(c_10190,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10189,c_7365])).

cnf(c_10193,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10190,c_54,c_3353])).

cnf(c_10201,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10193,c_8826])).

cnf(c_28411,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28410,c_10201])).

cnf(c_28412,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_28411])).

cnf(c_1931,plain,
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
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2912,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1931])).

cnf(c_3120,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2912,c_2899])).

cnf(c_10521,plain,
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
    inference(superposition,[status(thm)],[c_3120,c_2910])).

cnf(c_1929,plain,
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
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2914,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1929])).

cnf(c_3068,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2914,c_2899])).

cnf(c_16446,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_10521,c_3068])).

cnf(c_16450,plain,
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
    inference(superposition,[status(thm)],[c_2915,c_16446])).

cnf(c_17327,plain,
    ( v1_funct_1(X2_57) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
    | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16450,c_46,c_49,c_55,c_56])).

cnf(c_17328,plain,
    ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
    | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(X2_57) != iProver_top
    | v1_xboole_0(X1_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_17327])).

cnf(c_17341,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2918,c_17328])).

cnf(c_52,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_53,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_17762,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17341,c_47,c_52,c_53])).

cnf(c_17771,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2921,c_17762])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3506,plain,
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
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_3852,plain,
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
    inference(instantiation,[status(thm)],[c_3506])).

cnf(c_4240,plain,
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
    inference(instantiation,[status(thm)],[c_3852])).

cnf(c_4647,plain,
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
    inference(instantiation,[status(thm)],[c_4240])).

cnf(c_5690,plain,
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
    inference(instantiation,[status(thm)],[c_4647])).

cnf(c_3526,plain,
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
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_3892,plain,
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
    inference(instantiation,[status(thm)],[c_3526])).

cnf(c_4323,plain,
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
    inference(instantiation,[status(thm)],[c_3892])).

cnf(c_4778,plain,
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
    inference(instantiation,[status(thm)],[c_4323])).

cnf(c_7659,plain,
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
    inference(instantiation,[status(thm)],[c_4778])).

cnf(c_7259,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(X0_57,X1_57,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) ),
    inference(instantiation,[status(thm)],[c_1933])).

cnf(c_12419,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
    inference(instantiation,[status(thm)],[c_7259])).

cnf(c_17878,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17771,c_44,c_43,c_42,c_41,c_40,c_39,c_37,c_36,c_35,c_34,c_33,c_32,c_5690,c_7659,c_12419])).

cnf(c_28413,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28412,c_17878])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_243,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_30,c_29,c_28])).

cnf(c_244,plain,
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
    inference(renaming,[status(thm)],[c_243])).

cnf(c_1914,plain,
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
    inference(subtyping,[status(esa)],[c_244])).

cnf(c_2928,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_3175,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2928,c_2899])).

cnf(c_12701,plain,
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
    inference(superposition,[status(thm)],[c_5967,c_3175])).

cnf(c_27191,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12701,c_46,c_47,c_52,c_53,c_54])).

cnf(c_27192,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_27191])).

cnf(c_27205,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5961,c_27192])).

cnf(c_27567,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27205,c_49,c_55,c_56,c_57])).

cnf(c_27577,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4032,c_27567])).

cnf(c_27578,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27577,c_4026,c_8817])).

cnf(c_27579,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27578,c_4032,c_17878])).

cnf(c_27580,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27579,c_4026,c_10201])).

cnf(c_27581,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_27580])).

cnf(c_31,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1928,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_4369,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_4032,c_1928])).

cnf(c_4541,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4026,c_4369])).

cnf(c_5965,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5961,c_4541])).

cnf(c_6134,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5965,c_5967])).

cnf(c_10052,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8817,c_6134])).

cnf(c_11559,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10052,c_10201])).

cnf(c_11560,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_11559])).

cnf(c_17882,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_17878,c_11560])).

cnf(c_17883,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_17882,c_17878])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28413,c_27581,c_17883,c_54,c_53,c_52,c_50,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.58/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.50  
% 7.58/1.50  ------  iProver source info
% 7.58/1.50  
% 7.58/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.50  git: non_committed_changes: false
% 7.58/1.50  git: last_make_outside_of_git: false
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  ------ Parsing...
% 7.58/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.50  ------ Proving...
% 7.58/1.50  ------ Problem Properties 
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  clauses                                 39
% 7.58/1.50  conjectures                             13
% 7.58/1.50  EPR                                     11
% 7.58/1.50  Horn                                    32
% 7.58/1.50  unary                                   16
% 7.58/1.50  binary                                  7
% 7.58/1.50  lits                                    146
% 7.58/1.50  lits eq                                 23
% 7.58/1.50  fd_pure                                 0
% 7.58/1.50  fd_pseudo                               0
% 7.58/1.50  fd_cond                                 0
% 7.58/1.50  fd_pseudo_cond                          1
% 7.58/1.50  AC symbols                              0
% 7.58/1.50  
% 7.58/1.50  ------ Input Options Time Limit: Unbounded
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  Current options:
% 7.58/1.50  ------ 
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ Proving...
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS status Theorem for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  fof(f22,conjecture,(
% 7.58/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f23,negated_conjecture,(
% 7.58/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.58/1.50    inference(negated_conjecture,[],[f22])).
% 7.58/1.50  
% 7.58/1.50  fof(f48,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f23])).
% 7.58/1.50  
% 7.58/1.50  fof(f49,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f62,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f61,plain,(
% 7.58/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f60,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f59,plain,(
% 7.58/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f58,plain,(
% 7.58/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f57,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f63,plain,(
% 7.58/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.58/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f49,f62,f61,f60,f59,f58,f57])).
% 7.58/1.50  
% 7.58/1.50  fof(f105,plain,(
% 7.58/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f19,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f42,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.58/1.50    inference(ennf_transformation,[],[f19])).
% 7.58/1.50  
% 7.58/1.50  fof(f43,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(flattening,[],[f42])).
% 7.58/1.50  
% 7.58/1.50  fof(f89,plain,(
% 7.58/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f43])).
% 7.58/1.50  
% 7.58/1.50  fof(f103,plain,(
% 7.58/1.50    v1_funct_1(sK4)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f14,axiom,(
% 7.58/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f34,plain,(
% 7.58/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f14])).
% 7.58/1.50  
% 7.58/1.50  fof(f35,plain,(
% 7.58/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f34])).
% 7.58/1.50  
% 7.58/1.50  fof(f53,plain,(
% 7.58/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.58/1.50    inference(nnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f81,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f53])).
% 7.58/1.50  
% 7.58/1.50  fof(f102,plain,(
% 7.58/1.50    r1_subset_1(sK2,sK3)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f98,plain,(
% 7.58/1.50    ~v1_xboole_0(sK2)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f100,plain,(
% 7.58/1.50    ~v1_xboole_0(sK3)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f1,axiom,(
% 7.58/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f50,plain,(
% 7.58/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.58/1.50    inference(nnf_transformation,[],[f1])).
% 7.58/1.50  
% 7.58/1.50  fof(f64,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f50])).
% 7.58/1.50  
% 7.58/1.50  fof(f5,axiom,(
% 7.58/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f69,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f5])).
% 7.58/1.50  
% 7.58/1.50  fof(f111,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.58/1.50    inference(definition_unfolding,[],[f64,f69])).
% 7.58/1.50  
% 7.58/1.50  fof(f101,plain,(
% 7.58/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f3,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f25,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f3])).
% 7.58/1.50  
% 7.58/1.50  fof(f67,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f112,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(definition_unfolding,[],[f67,f69])).
% 7.58/1.50  
% 7.58/1.50  fof(f108,plain,(
% 7.58/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f106,plain,(
% 7.58/1.50    v1_funct_1(sK5)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f20,axiom,(
% 7.58/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f44,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f20])).
% 7.58/1.50  
% 7.58/1.50  fof(f45,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f44])).
% 7.58/1.50  
% 7.58/1.50  fof(f55,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(nnf_transformation,[],[f45])).
% 7.58/1.50  
% 7.58/1.50  fof(f56,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f55])).
% 7.58/1.50  
% 7.58/1.50  fof(f90,plain,(
% 7.58/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f56])).
% 7.58/1.50  
% 7.58/1.50  fof(f117,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(equality_resolution,[],[f90])).
% 7.58/1.50  
% 7.58/1.50  fof(f21,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f46,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f21])).
% 7.58/1.50  
% 7.58/1.50  fof(f47,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f46])).
% 7.58/1.50  
% 7.58/1.50  fof(f93,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f94,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f95,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f4,axiom,(
% 7.58/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f26,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f4])).
% 7.58/1.50  
% 7.58/1.50  fof(f68,plain,(
% 7.58/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f26])).
% 7.58/1.50  
% 7.58/1.50  fof(f97,plain,(
% 7.58/1.50    ~v1_xboole_0(sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f107,plain,(
% 7.58/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f15,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f36,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f15])).
% 7.58/1.50  
% 7.58/1.50  fof(f83,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f36])).
% 7.58/1.50  
% 7.58/1.50  fof(f17,axiom,(
% 7.58/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f38,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.58/1.50    inference(ennf_transformation,[],[f17])).
% 7.58/1.50  
% 7.58/1.50  fof(f39,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.58/1.50    inference(flattening,[],[f38])).
% 7.58/1.50  
% 7.58/1.50  fof(f86,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f39])).
% 7.58/1.50  
% 7.58/1.50  fof(f16,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f24,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.58/1.50    inference(pure_predicate_removal,[],[f16])).
% 7.58/1.50  
% 7.58/1.50  fof(f37,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f24])).
% 7.58/1.50  
% 7.58/1.50  fof(f84,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f37])).
% 7.58/1.50  
% 7.58/1.50  fof(f18,axiom,(
% 7.58/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f40,plain,(
% 7.58/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f18])).
% 7.58/1.50  
% 7.58/1.50  fof(f41,plain,(
% 7.58/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(flattening,[],[f40])).
% 7.58/1.50  
% 7.58/1.50  fof(f54,plain,(
% 7.58/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(nnf_transformation,[],[f41])).
% 7.58/1.50  
% 7.58/1.50  fof(f87,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f54])).
% 7.58/1.50  
% 7.58/1.50  fof(f10,axiom,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f31,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f10])).
% 7.58/1.50  
% 7.58/1.50  fof(f75,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f31])).
% 7.58/1.50  
% 7.58/1.50  fof(f12,axiom,(
% 7.58/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f32,plain,(
% 7.58/1.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(ennf_transformation,[],[f12])).
% 7.58/1.50  
% 7.58/1.50  fof(f78,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f32])).
% 7.58/1.50  
% 7.58/1.50  fof(f11,axiom,(
% 7.58/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f76,plain,(
% 7.58/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.58/1.50    inference(cnf_transformation,[],[f11])).
% 7.58/1.50  
% 7.58/1.50  fof(f9,axiom,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f30,plain,(
% 7.58/1.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f9])).
% 7.58/1.50  
% 7.58/1.50  fof(f74,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f30])).
% 7.58/1.50  
% 7.58/1.50  fof(f2,axiom,(
% 7.58/1.50    v1_xboole_0(k1_xboole_0)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f66,plain,(
% 7.58/1.50    v1_xboole_0(k1_xboole_0)),
% 7.58/1.50    inference(cnf_transformation,[],[f2])).
% 7.58/1.50  
% 7.58/1.50  fof(f6,axiom,(
% 7.58/1.50    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f27,plain,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f6])).
% 7.58/1.50  
% 7.58/1.50  fof(f70,plain,(
% 7.58/1.50    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f27])).
% 7.58/1.50  
% 7.58/1.50  fof(f7,axiom,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f28,plain,(
% 7.58/1.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f7])).
% 7.58/1.50  
% 7.58/1.50  fof(f71,plain,(
% 7.58/1.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f28])).
% 7.58/1.50  
% 7.58/1.50  fof(f77,plain,(
% 7.58/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.58/1.50    inference(cnf_transformation,[],[f11])).
% 7.58/1.50  
% 7.58/1.50  fof(f8,axiom,(
% 7.58/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f29,plain,(
% 7.58/1.50    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(ennf_transformation,[],[f8])).
% 7.58/1.50  
% 7.58/1.50  fof(f51,plain,(
% 7.58/1.50    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(nnf_transformation,[],[f29])).
% 7.58/1.50  
% 7.58/1.50  fof(f72,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f51])).
% 7.58/1.50  
% 7.58/1.50  fof(f13,axiom,(
% 7.58/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f33,plain,(
% 7.58/1.50    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(ennf_transformation,[],[f13])).
% 7.58/1.50  
% 7.58/1.50  fof(f52,plain,(
% 7.58/1.50    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(nnf_transformation,[],[f33])).
% 7.58/1.50  
% 7.58/1.50  fof(f80,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f52])).
% 7.58/1.50  
% 7.58/1.50  fof(f99,plain,(
% 7.58/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f104,plain,(
% 7.58/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f96,plain,(
% 7.58/1.50    ~v1_xboole_0(sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f91,plain,(
% 7.58/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f56])).
% 7.58/1.50  
% 7.58/1.50  fof(f116,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(equality_resolution,[],[f91])).
% 7.58/1.50  
% 7.58/1.50  fof(f109,plain,(
% 7.58/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  cnf(c_35,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1924,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_35]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2918,plain,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1924]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_24,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.58/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1933,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2910,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1933]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5376,plain,
% 7.58/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2918,c_2910]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_37,negated_conjecture,
% 7.58/1.50      ( v1_funct_1(sK4) ),
% 7.58/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3476,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1933]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3761,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3476]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5967,plain,
% 7.58/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_5376,c_37,c_35,c_3761]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17,plain,
% 7.58/1.50      ( ~ r1_subset_1(X0,X1)
% 7.58/1.50      | r1_xboole_0(X0,X1)
% 7.58/1.50      | v1_xboole_0(X0)
% 7.58/1.50      | v1_xboole_0(X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_38,negated_conjecture,
% 7.58/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.58/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_618,plain,
% 7.58/1.50      ( r1_xboole_0(X0,X1)
% 7.58/1.50      | v1_xboole_0(X0)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | sK3 != X1
% 7.58/1.50      | sK2 != X0 ),
% 7.58/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_38]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_619,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.58/1.50      inference(unflattening,[status(thm)],[c_618]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_42,negated_conjecture,
% 7.58/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.58/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_40,negated_conjecture,
% 7.58/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.58/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_621,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_619,c_42,c_40]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1913,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_621]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2929,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1,plain,
% 7.58/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.58/1.50      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f111]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1949,plain,
% 7.58/1.50      ( ~ r1_xboole_0(X0_57,X1_57)
% 7.58/1.50      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2896,plain,
% 7.58/1.50      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4026,plain,
% 7.58/1.50      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2929,c_2896]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_39,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1921,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_39]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2921,plain,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1921]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f112]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1947,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.58/1.50      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2898,plain,
% 7.58/1.50      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1947]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4032,plain,
% 7.58/1.50      ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2921,c_2898]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_32,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1927,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_32]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2915,plain,
% 7.58/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1927]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5375,plain,
% 7.58/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
% 7.58/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2915,c_2910]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_34,negated_conjecture,
% 7.58/1.50      ( v1_funct_1(sK5) ),
% 7.58/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3471,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1933]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3756,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3471]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5961,plain,
% 7.58/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_5375,c_34,c_32,c_3756]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.58/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_30,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_29,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_236,plain,
% 7.58/1.50      ( ~ v1_funct_1(X3)
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_27,c_30,c_29,c_28]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_237,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_236]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1915,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | ~ v1_funct_1(X3_57)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X4_57)
% 7.58/1.50      | v1_xboole_0(X5_57)
% 7.58/1.50      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_237]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2927,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 7.58/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X3_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | ~ v1_xboole_0(X1)
% 7.58/1.50      | v1_xboole_0(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1946,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.58/1.50      | ~ v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X0_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2899,plain,
% 7.58/1.50      ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1946]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3147,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X0_57) = X2_57
% 7.58/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_2927,c_2899]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11583,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,X0_57,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_57,X0_57,sK3))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK3),sK1,k1_tmap_1(X2_57,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_funct_1(sK5) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.58/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5961,c_3147]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_43,negated_conjecture,
% 7.58/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_46,plain,
% 7.58/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_49,plain,
% 7.58/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_55,plain,
% 7.58/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_33,negated_conjecture,
% 7.58/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_56,plain,
% 7.58/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_57,plain,
% 7.58/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13800,plain,
% 7.58/1.50      ( v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK3),sK1,k1_tmap_1(X2_57,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,X0_57,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_57,X0_57,sK3))
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_11583,c_46,c_49,c_55,c_56,c_57]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13801,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,X0_57,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_57,X0_57,sK3))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X2_57,X0_57,sK3),sK1,k1_tmap_1(X2_57,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_13800]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13816,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k9_subset_1(sK0,X0_57,sK3))
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4032,c_13801]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13825,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_57,sK3)))
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_13816,c_4032]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_50,plain,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13912,plain,
% 7.58/1.50      ( m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_57,sK3)))
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_13825,c_50]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13913,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k1_setfam_1(k2_tarski(X0_57,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_57,sK3)))
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,X0_57,sK3),sK1,k1_tmap_1(sK0,sK1,X0_57,sK3,X1_57,sK5),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_13912]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13927,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
% 7.58/1.50      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,X0_57,k1_xboole_0)
% 7.58/1.50      | v1_funct_2(X0_57,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4026,c_13913]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_18,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1934,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | v1_relat_1(X0_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_18]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2909,plain,
% 7.58/1.50      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.58/1.50      | v1_relat_1(X0_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1934]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4199,plain,
% 7.58/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2915,c_2909]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_20,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | v1_partfun1(X0,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v1_xboole_0(X2) ),
% 7.58/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_19,plain,
% 7.58/1.50      ( v4_relat_1(X0,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_23,plain,
% 7.58/1.50      ( ~ v1_partfun1(X0,X1)
% 7.58/1.50      | ~ v4_relat_1(X0,X1)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_573,plain,
% 7.58/1.50      ( ~ v1_partfun1(X0,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(resolution,[status(thm)],[c_19,c_23]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_577,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_partfun1(X0,X1)
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_573,c_23,c_19,c_18]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_578,plain,
% 7.58/1.50      ( ~ v1_partfun1(X0,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_577]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_631,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(resolution,[status(thm)],[c_20,c_578]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_635,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_631,c_23,c_20,c_19,c_18]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_636,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | k1_relat_1(X0) = X1 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_635]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1912,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | k1_relat_1(X0_57) = X1_57 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_636]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2930,plain,
% 7.58/1.50      ( k1_relat_1(X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1912]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6578,plain,
% 7.58/1.50      ( k1_relat_1(sK5) = sK3
% 7.58/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.58/1.50      | v1_funct_1(sK5) != iProver_top
% 7.58/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2915,c_2930]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3461,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | k1_relat_1(sK5) = X0_57 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1912]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3750,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3461]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6599,plain,
% 7.58/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_6578,c_43,c_34,c_33,c_32,c_3750]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10,plain,
% 7.58/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.58/1.50      | ~ v1_relat_1(X1)
% 7.58/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1940,plain,
% 7.58/1.50      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 7.58/1.50      | ~ v1_relat_1(X1_57)
% 7.58/1.50      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2905,plain,
% 7.58/1.50      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1940]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6612,plain,
% 7.58/1.50      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(X0_57,sK3) != iProver_top
% 7.58/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_6599,c_2905]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3349,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | v1_relat_1(sK5) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1934]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3350,plain,
% 7.58/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.58/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_3349]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6727,plain,
% 7.58/1.50      ( r1_xboole_0(X0_57,sK3) != iProver_top
% 7.58/1.50      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_6612,c_57,c_3350]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6728,plain,
% 7.58/1.50      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(X0_57,sK3) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_6727]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6735,plain,
% 7.58/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2929,c_6728]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13,plain,
% 7.58/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1937,plain,
% 7.58/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57)
% 7.58/1.50      | ~ v1_relat_1(X0_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2906,plain,
% 7.58/1.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57) = iProver_top
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1937]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7540,plain,
% 7.58/1.50      ( r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
% 7.58/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_6735,c_2906]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_12,plain,
% 7.58/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1938,plain,
% 7.58/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7543,plain,
% 7.58/1.50      ( r1_tarski(k1_xboole_0,sK2) = iProver_top
% 7.58/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_7540,c_1938]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8504,plain,
% 7.58/1.50      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_7543,c_57,c_3350]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9,plain,
% 7.58/1.50      ( ~ r1_tarski(X0,X1)
% 7.58/1.50      | ~ v1_relat_1(X2)
% 7.58/1.50      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1941,plain,
% 7.58/1.50      ( ~ r1_tarski(X0_57,X1_57)
% 7.58/1.50      | ~ v1_relat_1(X2_57)
% 7.58/1.50      | k9_relat_1(k7_relat_1(X2_57,X1_57),X0_57) = k9_relat_1(X2_57,X0_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2904,plain,
% 7.58/1.50      ( k9_relat_1(k7_relat_1(X0_57,X1_57),X2_57) = k9_relat_1(X0_57,X2_57)
% 7.58/1.50      | r1_tarski(X2_57,X1_57) != iProver_top
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8509,plain,
% 7.58/1.50      ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_8504,c_2904]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8517,plain,
% 7.58/1.50      ( k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4199,c_8509]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2,plain,
% 7.58/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1948,plain,
% 7.58/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2897,plain,
% 7.58/1.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1948]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5,plain,
% 7.58/1.50      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1945,plain,
% 7.58/1.50      ( v1_relat_1(X0_57) | ~ v1_xboole_0(X0_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2900,plain,
% 7.58/1.50      ( v1_relat_1(X0_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1945]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3927,plain,
% 7.58/1.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2897,c_2900]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6,plain,
% 7.58/1.50      ( ~ v1_relat_1(X0)
% 7.58/1.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1944,plain,
% 7.58/1.50      ( ~ v1_relat_1(X0_57)
% 7.58/1.50      | k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2901,plain,
% 7.58/1.50      ( k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57)
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4122,plain,
% 7.58/1.50      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3927,c_2901]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11,plain,
% 7.58/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1939,plain,
% 7.58/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4123,plain,
% 7.58/1.50      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_4122,c_1938,c_1939]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8522,plain,
% 7.58/1.50      ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_8517,c_4123,c_6735]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8,plain,
% 7.58/1.50      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1942,plain,
% 7.58/1.50      ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.58/1.50      | ~ v1_relat_1(X0_57)
% 7.58/1.50      | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2903,plain,
% 7.58/1.50      ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
% 7.58/1.50      | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1942]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8622,plain,
% 7.58/1.50      ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
% 7.58/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_8522,c_2903]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8623,plain,
% 7.58/1.50      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
% 7.58/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_8622,c_6599]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8809,plain,
% 7.58/1.50      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_8623,c_57,c_3350]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14,plain,
% 7.58/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1936,plain,
% 7.58/1.50      ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.58/1.50      | ~ v1_relat_1(X0_57)
% 7.58/1.50      | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2907,plain,
% 7.58/1.50      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6611,plain,
% 7.58/1.50      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(sK3,X0_57) != iProver_top
% 7.58/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_6599,c_2907]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6718,plain,
% 7.58/1.50      ( r1_xboole_0(sK3,X0_57) != iProver_top
% 7.58/1.50      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_6611,c_57,c_3350]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6719,plain,
% 7.58/1.50      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(sK3,X0_57) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_6718]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8817,plain,
% 7.58/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_8809,c_6719]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13936,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
% 7.58/1.50      | k2_partfun1(sK2,sK1,X0_57,k1_xboole_0) != k1_xboole_0
% 7.58/1.50      | v1_funct_2(X0_57,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.50      inference(light_normalisation,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_13927,c_4026,c_8817]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_47,plain,
% 7.58/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_41,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_48,plain,
% 7.58/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28399,plain,
% 7.58/1.50      ( v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
% 7.58/1.50      | k2_partfun1(sK2,sK1,X0_57,k1_xboole_0) != k1_xboole_0
% 7.58/1.50      | v1_funct_2(X0_57,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_13936,c_47,c_48]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28400,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X0_57,sK5),sK2) = X0_57
% 7.58/1.50      | k2_partfun1(sK2,sK1,X0_57,k1_xboole_0) != k1_xboole_0
% 7.58/1.50      | v1_funct_2(X0_57,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_28399]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28410,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5967,c_28400]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4200,plain,
% 7.58/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2918,c_2909]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6579,plain,
% 7.58/1.50      ( k1_relat_1(sK4) = sK2
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top
% 7.58/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2918,c_2930]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36,negated_conjecture,
% 7.58/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3466,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK4,X0_57,X1_57)
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | k1_relat_1(sK4) = X0_57 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1912]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3753,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3466]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7365,plain,
% 7.58/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_6579,c_43,c_37,c_36,c_35,c_3753]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7377,plain,
% 7.58/1.50      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(sK2,X0_57) != iProver_top
% 7.58/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_7365,c_2907]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_54,plain,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3352,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | v1_relat_1(sK4) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1934]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3353,plain,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_3352]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8825,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,X0_57) != iProver_top
% 7.58/1.50      | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_7377,c_54,c_3353]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8826,plain,
% 7.58/1.50      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.58/1.50      | r1_xboole_0(sK2,X0_57) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_8825]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8833,plain,
% 7.58/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2929,c_8826]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8993,plain,
% 7.58/1.50      ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
% 7.58/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_8833,c_2906]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8996,plain,
% 7.58/1.50      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 7.58/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_8993,c_1938]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9466,plain,
% 7.58/1.50      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_8996,c_54,c_3353]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9471,plain,
% 7.58/1.50      ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
% 7.58/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_9466,c_2904]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9869,plain,
% 7.58/1.50      ( k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4200,c_9471]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9871,plain,
% 7.58/1.50      ( k9_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_9869,c_4123,c_8833]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10189,plain,
% 7.58/1.50      ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top
% 7.58/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_9871,c_2903]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10190,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top
% 7.58/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_10189,c_7365]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10193,plain,
% 7.58/1.50      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_10190,c_54,c_3353]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10201,plain,
% 7.58/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_10193,c_8826]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28411,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.50      | k1_xboole_0 != k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_28410,c_10201]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28412,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.58/1.50      inference(equality_resolution_simp,[status(thm)],[c_28411]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1931,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | ~ v1_funct_1(X3_57)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X4_57)
% 7.58/1.50      | v1_xboole_0(X5_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_28]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2912,plain,
% 7.58/1.50      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57))) = iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X3_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X5_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1931]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3120,plain,
% 7.58/1.50      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_57,X4_57,X1_57),X2_57))) = iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X3_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_2912,c_2899]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10521,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,X1_57,X2_57),X3_57,k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57) = k7_relat_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57)
% 7.58/1.50      | v1_funct_2(X5_57,X2_57,X3_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X4_57,X1_57,X3_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X2_57,X3_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X4_57) != iProver_top
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57)) != iProver_top
% 7.58/1.50      | v1_xboole_0(X3_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3120,c_2910]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1929,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | ~ v1_funct_1(X3_57)
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57))
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X4_57)
% 7.58/1.50      | v1_xboole_0(X5_57) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2914,plain,
% 7.58/1.50      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X3_57) != iProver_top
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57)) = iProver_top
% 7.58/1.50      | v1_xboole_0(X5_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1929]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3068,plain,
% 7.58/1.50      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X3_57,X4_57,X2_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X5_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X3_57) != iProver_top
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57)) = iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_2914,c_2899]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16446,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,X1_57,X2_57),X3_57,k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57) = k7_relat_1(k1_tmap_1(X0_57,X3_57,X1_57,X2_57,X4_57,X5_57),X6_57)
% 7.58/1.50      | v1_funct_2(X5_57,X2_57,X3_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X4_57,X1_57,X3_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X2_57,X3_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X4_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X2_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X3_57) = iProver_top ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_10521,c_3068]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16450,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
% 7.58/1.50      | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
% 7.58/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | v1_funct_1(sK5) != iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.58/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2915,c_16446]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17327,plain,
% 7.58/1.50      ( v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
% 7.58/1.50      | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_16450,c_46,c_49,c_55,c_56]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17328,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,X1_57,sK3),sK1,k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,X1_57,sK3,X2_57,sK5),X3_57)
% 7.58/1.50      | v1_funct_2(X2_57,X1_57,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_17327]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17341,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top
% 7.58/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2918,c_17328]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_52,plain,
% 7.58/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_53,plain,
% 7.58/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17762,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57) = k7_relat_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),X1_57)
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17341,c_47,c_52,c_53]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17771,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57)
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2921,c_17762]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_44,negated_conjecture,
% 7.58/1.50      ( ~ v1_xboole_0(sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3506,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ v1_funct_2(sK4,X3_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
% 7.58/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK4,X0_57))
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X4_57)
% 7.58/1.50      | v1_xboole_0(X3_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1929]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3852,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 7.58/1.50      | ~ v1_funct_2(sK4,X2_57,X1_57)
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
% 7.58/1.50      | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK4,sK5))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X3_57)
% 7.58/1.50      | v1_xboole_0(X0_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3506]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4240,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,X0_57,sK1)
% 7.58/1.50      | ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_57))
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X1_57,sK1,sK2,X0_57,sK4,sK5))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X0_57)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | v1_xboole_0(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3852]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4647,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.58/1.50      | ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_57))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_57))
% 7.58/1.50      | v1_funct_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X0_57)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | v1_xboole_0(sK3)
% 7.58/1.50      | v1_xboole_0(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_4240]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5690,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.58/1.50      | ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.58/1.50      | v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | v1_xboole_0(sK3)
% 7.58/1.50      | v1_xboole_0(sK2)
% 7.58/1.50      | v1_xboole_0(sK0) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_4647]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3526,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ v1_funct_2(sK4,X3_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(X4_57))
% 7.58/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X4_57))
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X4_57,X2_57,X3_57,X1_57,sK4,X0_57),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X4_57,X3_57,X1_57),X2_57)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X4_57)
% 7.58/1.50      | v1_xboole_0(X3_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1931]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3892,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 7.58/1.50      | ~ v1_funct_2(sK4,X2_57,X1_57)
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X3_57))
% 7.58/1.50      | ~ m1_subset_1(X2_57,k1_zfmisc_1(X3_57))
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X3_57,X1_57,X2_57,X0_57,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3_57,X2_57,X0_57),X1_57)))
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_57,X1_57)))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X3_57)
% 7.58/1.50      | v1_xboole_0(X0_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3526]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4323,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,X0_57,sK1)
% 7.58/1.50      | ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X1_57,sK1,sK2,X0_57,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X1_57,sK2,X0_57),sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_57))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X0_57)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | v1_xboole_0(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3892]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4778,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.58/1.50      | ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | m1_subset_1(k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0_57,sK2,sK3),sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_57))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_57))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(X0_57)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | v1_xboole_0(sK3)
% 7.58/1.50      | v1_xboole_0(sK2) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_4323]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7659,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.58/1.50      | ~ v1_funct_2(sK4,sK2,sK1)
% 7.58/1.50      | m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.58/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.58/1.50      | ~ v1_funct_1(sK5)
% 7.58/1.50      | ~ v1_funct_1(sK4)
% 7.58/1.50      | v1_xboole_0(sK1)
% 7.58/1.50      | v1_xboole_0(sK3)
% 7.58/1.50      | v1_xboole_0(sK2)
% 7.58/1.50      | v1_xboole_0(sK0) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_4778]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7259,plain,
% 7.58/1.50      ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.58/1.50      | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
% 7.58/1.50      | k2_partfun1(X0_57,X1_57,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X2_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1933]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_12419,plain,
% 7.58/1.50      ( ~ m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
% 7.58/1.50      | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_7259]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17878,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_57) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17771,c_44,c_43,c_42,c_41,c_40,c_39,c_37,c_36,c_35,
% 7.58/1.50                 c_34,c_33,c_32,c_5690,c_7659,c_12419]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_28413,plain,
% 7.58/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_28412,c_17878]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_26,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_243,plain,
% 7.58/1.50      ( ~ v1_funct_1(X3)
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_26,c_30,c_29,c_28]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_244,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | v1_xboole_0(X1)
% 7.58/1.50      | v1_xboole_0(X2)
% 7.58/1.50      | v1_xboole_0(X4)
% 7.58/1.50      | v1_xboole_0(X5)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_243]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1914,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.58/1.50      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.58/1.50      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.58/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.58/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.58/1.50      | ~ v1_funct_1(X0_57)
% 7.58/1.50      | ~ v1_funct_1(X3_57)
% 7.58/1.50      | v1_xboole_0(X2_57)
% 7.58/1.50      | v1_xboole_0(X1_57)
% 7.58/1.50      | v1_xboole_0(X4_57)
% 7.58/1.50      | v1_xboole_0(X5_57)
% 7.58/1.50      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_244]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2928,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 7.58/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X3_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3175,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X4_57) = X5_57
% 7.58/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.58/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.58/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.58/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(X4_57) = iProver_top ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_2928,c_2899]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_12701,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.58/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.58/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5967,c_3175]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27191,plain,
% 7.58/1.50      ( v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.58/1.50      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_12701,c_46,c_47,c_52,c_53,c_54]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27192,plain,
% 7.58/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.58/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.58/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.58/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_27191]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27205,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.58/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.58/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | v1_funct_1(sK5) != iProver_top
% 7.58/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5961,c_27192]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27567,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_27205,c_49,c_55,c_56,c_57]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27577,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4032,c_27567]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27578,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_27577,c_4026,c_8817]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27579,plain,
% 7.58/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_27578,c_4032,c_17878]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27580,plain,
% 7.58/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | k1_xboole_0 != k1_xboole_0
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_27579,c_4026,c_10201]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27581,plain,
% 7.58/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.58/1.50      inference(equality_resolution_simp,[status(thm)],[c_27580]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_31,negated_conjecture,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1928,negated_conjecture,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_31]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4369,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_4032,c_1928]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4541,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_4026,c_4369]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5965,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_5961,c_4541]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6134,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_5965,c_5967]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10052,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_8817,c_6134]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11559,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_10052,c_10201]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11560,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_11559]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17882,plain,
% 7.58/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_17878,c_11560]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17883,plain,
% 7.58/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_17882,c_17878]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(contradiction,plain,
% 7.58/1.50      ( $false ),
% 7.58/1.50      inference(minisat,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_28413,c_27581,c_17883,c_54,c_53,c_52,c_50,c_48]) ).
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  ------                               Statistics
% 7.58/1.50  
% 7.58/1.50  ------ Selected
% 7.58/1.50  
% 7.58/1.50  total_time:                             0.992
% 7.58/1.50  
%------------------------------------------------------------------------------
