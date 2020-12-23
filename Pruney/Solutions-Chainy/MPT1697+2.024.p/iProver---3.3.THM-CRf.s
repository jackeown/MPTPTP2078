%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:27 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  300 (5671 expanded)
%              Number of clauses        :  198 (1543 expanded)
%              Number of leaves         :   27 (2100 expanded)
%              Depth                    :   28
%              Number of atoms          : 1360 (67336 expanded)
%              Number of equality atoms :  533 (15486 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f100,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f107,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f104,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    v1_funct_1(sK4) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f115,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f92,plain,(
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

fof(f93,plain,(
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

fof(f94,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f103,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f99,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f106,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
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

fof(f116,plain,(
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
    inference(equality_resolution,[],[f89])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f108,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_757,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_1801,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_790,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1771,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_790])).

cnf(c_2627,plain,
    ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
    inference(superposition,[status(thm)],[c_1801,c_1771])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_764,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1794,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1789,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_7091,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1789])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2405,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_2750,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(instantiation,[status(thm)],[c_2405])).

cnf(c_7353,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7091,c_33,c_31,c_2750])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_761,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1797,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_7092,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1789])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2410,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_2755,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_7359,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7092,c_36,c_34,c_2755])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f115])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f92])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f93])).

cnf(c_27,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_441,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_29,c_28,c_27])).

cnf(c_442,plain,
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
    inference(renaming,[status(thm)],[c_441])).

cnf(c_750,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
    | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_1808,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_788,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1773,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
    | v1_xboole_0(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_2083,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1808,c_1773])).

cnf(c_13884,plain,
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
    inference(superposition,[status(thm)],[c_7359,c_2083])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_45,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_46,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18122,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13884,c_45,c_46,c_51,c_52,c_53])).

cnf(c_18123,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_18122])).

cnf(c_18136,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7353,c_18123])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_48,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18474,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18136,c_48,c_54,c_55,c_56])).

cnf(c_18484,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_18474])).

cnf(c_37,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_758,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1800,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_16,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_776,plain,
    ( ~ r1_subset_1(X0_57,X1_57)
    | r1_xboole_0(X0_57,X1_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1783,plain,
    ( r1_subset_1(X0_57,X1_57) != iProver_top
    | r1_xboole_0(X0_57,X1_57) = iProver_top
    | v1_xboole_0(X1_57) = iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_776])).

cnf(c_4397,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1783])).

cnf(c_50,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2315,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_2316,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2315])).

cnf(c_4780,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4397,c_46,c_48,c_50,c_2316])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_791,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1770,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_791])).

cnf(c_4786,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4780,c_1770])).

cnf(c_18485,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18484,c_4786])).

cnf(c_18486,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18485,c_2627])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1784,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_3496,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1784])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_773,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | v1_partfun1(X0_57,X1_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | v1_xboole_0(X2_57) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1786,plain,
    ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | v1_partfun1(X0_57,X1_57) = iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_5514,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1786])).

cnf(c_2430,plain,
    ( ~ v1_funct_2(sK4,X0_57,X1_57)
    | v1_partfun1(sK4,X0_57)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_57) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_2804,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2430])).

cnf(c_2805,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2804])).

cnf(c_6217,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5514,c_45,c_51,c_52,c_53,c_2805])).

cnf(c_22,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_771,plain,
    ( ~ v1_partfun1(X0_57,X1_57)
    | ~ v4_relat_1(X0_57,X1_57)
    | ~ v1_relat_1(X0_57)
    | k1_relat_1(X0_57) = X1_57 ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1788,plain,
    ( k1_relat_1(X0_57) = X1_57
    | v1_partfun1(X0_57,X1_57) != iProver_top
    | v4_relat_1(X0_57,X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_7156,plain,
    ( k1_relat_1(sK4) = sK2
    | v4_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6217,c_1788])).

cnf(c_2268,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_774,plain,
    ( v4_relat_1(X0_57,X1_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2310,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_2542,plain,
    ( ~ v1_partfun1(sK4,X0_57)
    | ~ v4_relat_1(sK4,X0_57)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0_57 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_2557,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2542])).

cnf(c_7498,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7156,c_42,c_36,c_35,c_34,c_2268,c_2310,c_2557,c_2804])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_779,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1780,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_7511,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7498,c_1780])).

cnf(c_2269,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2268])).

cnf(c_7793,plain,
    ( r1_xboole_0(sK2,X0_57) != iProver_top
    | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7511,c_53,c_2269])).

cnf(c_7794,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_7793])).

cnf(c_7801,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4780,c_7794])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_780,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57)
    | ~ v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1779,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_8181,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7801,c_1779])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_781,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_8184,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8181,c_781])).

cnf(c_8922,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8184,c_53,c_2269])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_784,plain,
    ( ~ r1_tarski(X0_57,X1_57)
    | ~ v1_relat_1(X2_57)
    | k9_relat_1(k7_relat_1(X2_57,X1_57),X0_57) = k9_relat_1(X2_57,X0_57) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1777,plain,
    ( k9_relat_1(k7_relat_1(X0_57,X1_57),X2_57) = k9_relat_1(X0_57,X2_57)
    | r1_tarski(X2_57,X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_8927,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8922,c_1777])).

cnf(c_9096,plain,
    ( k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3496,c_8927])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_789,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_57)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1772,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_789])).

cnf(c_3497,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_1784])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_787,plain,
    ( ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1774,plain,
    ( k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_4390,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3497,c_1774])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_782,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_4391,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4390,c_781,c_782])).

cnf(c_9102,plain,
    ( k9_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9096,c_4391,c_7801])).

cnf(c_7,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_785,plain,
    ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1776,plain,
    ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_785])).

cnf(c_9278,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9102,c_1776])).

cnf(c_9279,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9278,c_7498])).

cnf(c_9473,plain,
    ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9279,c_53,c_2269])).

cnf(c_9482,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9473,c_7794])).

cnf(c_18487,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18486,c_4786,c_9482])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_432,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_29,c_28,c_27])).

cnf(c_433,plain,
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
    inference(renaming,[status(thm)],[c_432])).

cnf(c_751,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ v1_funct_2(X3_57,X4_57,X2_57)
    | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | ~ v1_funct_1(X3_57)
    | v1_xboole_0(X1_57)
    | v1_xboole_0(X2_57)
    | v1_xboole_0(X4_57)
    | v1_xboole_0(X5_57)
    | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
    | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
    inference(subtyping,[status(esa)],[c_433])).

cnf(c_1807,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2055,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1807,c_1773])).

cnf(c_11714,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
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
    inference(superposition,[status(thm)],[c_7359,c_2055])).

cnf(c_13655,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11714,c_45,c_46,c_51,c_52,c_53])).

cnf(c_13656,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_13655])).

cnf(c_13669,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7353,c_13656])).

cnf(c_14785,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13669,c_48,c_54,c_55,c_56])).

cnf(c_14795,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2627,c_14785])).

cnf(c_14796,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14795,c_4786])).

cnf(c_14797,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14796,c_2627])).

cnf(c_14798,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14797,c_4786,c_9482])).

cnf(c_3495,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1784])).

cnf(c_5513,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1786])).

cnf(c_2425,plain,
    ( ~ v1_funct_2(sK5,X0_57,X1_57)
    | v1_partfun1(sK5,X0_57)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_57) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_2801,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2425])).

cnf(c_2802,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2801])).

cnf(c_5930,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5513,c_45,c_54,c_55,c_56,c_2802])).

cnf(c_7157,plain,
    ( k1_relat_1(sK5) = sK3
    | v4_relat_1(sK5,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5930,c_1788])).

cnf(c_2265,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_2307,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_2514,plain,
    ( ~ v1_partfun1(sK5,X0_57)
    | ~ v4_relat_1(sK5,X0_57)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = X0_57 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_3198,plain,
    ( ~ v1_partfun1(sK5,sK3)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_7544,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7157,c_42,c_33,c_32,c_31,c_2265,c_2307,c_2801,c_3198])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_783,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1778,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_7558,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7544,c_1778])).

cnf(c_2266,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2265])).

cnf(c_8453,plain,
    ( r1_xboole_0(X0_57,sK3) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7558,c_56,c_2266])).

cnf(c_8454,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8453])).

cnf(c_8461,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4780,c_8454])).

cnf(c_8535,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8461,c_1779])).

cnf(c_8538,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8535,c_781])).

cnf(c_8932,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8538,c_56,c_2266])).

cnf(c_8937,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_8932,c_1777])).

cnf(c_10946,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3495,c_8937])).

cnf(c_10955,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10946,c_4391,c_8461])).

cnf(c_10978,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10955,c_1776])).

cnf(c_10979,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10978,c_7544])).

cnf(c_11456,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10979,c_56,c_2266])).

cnf(c_7557,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7544,c_1780])).

cnf(c_8171,plain,
    ( r1_xboole_0(sK3,X0_57) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7557,c_56,c_2266])).

cnf(c_8172,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_8171])).

cnf(c_11465,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11456,c_8172])).

cnf(c_30,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_765,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2888,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2627,c_765])).

cnf(c_4790,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4786,c_2888])).

cnf(c_7357,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7353,c_4790])).

cnf(c_7646,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7357,c_7359])).

cnf(c_9889,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9482,c_7646])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18487,c_14798,c_11465,c_9889,c_49,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.71/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.71/1.48  
% 7.71/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.48  
% 7.71/1.48  ------  iProver source info
% 7.71/1.48  
% 7.71/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.48  git: non_committed_changes: false
% 7.71/1.48  git: last_make_outside_of_git: false
% 7.71/1.48  
% 7.71/1.48  ------ 
% 7.71/1.48  ------ Parsing...
% 7.71/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.48  
% 7.71/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.71/1.48  
% 7.71/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.48  
% 7.71/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.48  ------ Proving...
% 7.71/1.48  ------ Problem Properties 
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  clauses                                 43
% 7.71/1.48  conjectures                             14
% 7.71/1.48  EPR                                     11
% 7.71/1.48  Horn                                    34
% 7.71/1.48  unary                                   16
% 7.71/1.48  binary                                  7
% 7.71/1.48  lits                                    161
% 7.71/1.48  lits eq                                 23
% 7.71/1.48  fd_pure                                 0
% 7.71/1.48  fd_pseudo                               0
% 7.71/1.48  fd_cond                                 0
% 7.71/1.48  fd_pseudo_cond                          1
% 7.71/1.48  AC symbols                              0
% 7.71/1.48  
% 7.71/1.48  ------ Input Options Time Limit: Unbounded
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  ------ 
% 7.71/1.48  Current options:
% 7.71/1.48  ------ 
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  ------ Proving...
% 7.71/1.48  
% 7.71/1.48  
% 7.71/1.48  % SZS status Theorem for theBenchmark.p
% 7.71/1.48  
% 7.71/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.48  
% 7.71/1.48  fof(f22,conjecture,(
% 7.71/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f23,negated_conjecture,(
% 7.71/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.71/1.48    inference(negated_conjecture,[],[f22])).
% 7.71/1.48  
% 7.71/1.48  fof(f48,plain,(
% 7.71/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.71/1.48    inference(ennf_transformation,[],[f23])).
% 7.71/1.48  
% 7.71/1.48  fof(f49,plain,(
% 7.71/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.71/1.48    inference(flattening,[],[f48])).
% 7.71/1.48  
% 7.71/1.48  fof(f62,plain,(
% 7.71/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.71/1.48    introduced(choice_axiom,[])).
% 7.71/1.48  
% 7.71/1.48  fof(f61,plain,(
% 7.71/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.71/1.48    introduced(choice_axiom,[])).
% 7.71/1.48  
% 7.71/1.48  fof(f60,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.71/1.48    introduced(choice_axiom,[])).
% 7.71/1.48  
% 7.71/1.48  fof(f59,plain,(
% 7.71/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.71/1.48    introduced(choice_axiom,[])).
% 7.71/1.48  
% 7.71/1.48  fof(f58,plain,(
% 7.71/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.71/1.48    introduced(choice_axiom,[])).
% 7.71/1.48  
% 7.71/1.48  fof(f57,plain,(
% 7.71/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.71/1.48    introduced(choice_axiom,[])).
% 7.71/1.48  
% 7.71/1.48  fof(f63,plain,(
% 7.71/1.48    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.71/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f49,f62,f61,f60,f59,f58,f57])).
% 7.71/1.48  
% 7.71/1.48  fof(f100,plain,(
% 7.71/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f2,axiom,(
% 7.71/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f26,plain,(
% 7.71/1.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.71/1.48    inference(ennf_transformation,[],[f2])).
% 7.71/1.48  
% 7.71/1.48  fof(f66,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.71/1.48    inference(cnf_transformation,[],[f26])).
% 7.71/1.48  
% 7.71/1.48  fof(f5,axiom,(
% 7.71/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f69,plain,(
% 7.71/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.71/1.48    inference(cnf_transformation,[],[f5])).
% 7.71/1.48  
% 7.71/1.48  fof(f111,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.71/1.48    inference(definition_unfolding,[],[f66,f69])).
% 7.71/1.48  
% 7.71/1.48  fof(f107,plain,(
% 7.71/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f19,axiom,(
% 7.71/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f42,plain,(
% 7.71/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.71/1.48    inference(ennf_transformation,[],[f19])).
% 7.71/1.48  
% 7.71/1.48  fof(f43,plain,(
% 7.71/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.71/1.48    inference(flattening,[],[f42])).
% 7.71/1.48  
% 7.71/1.48  fof(f88,plain,(
% 7.71/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f43])).
% 7.71/1.48  
% 7.71/1.48  fof(f105,plain,(
% 7.71/1.48    v1_funct_1(sK5)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f104,plain,(
% 7.71/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f102,plain,(
% 7.71/1.48    v1_funct_1(sK4)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f20,axiom,(
% 7.71/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f44,plain,(
% 7.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.71/1.48    inference(ennf_transformation,[],[f20])).
% 7.71/1.48  
% 7.71/1.48  fof(f45,plain,(
% 7.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.71/1.48    inference(flattening,[],[f44])).
% 7.71/1.48  
% 7.71/1.48  fof(f55,plain,(
% 7.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.71/1.48    inference(nnf_transformation,[],[f45])).
% 7.71/1.48  
% 7.71/1.48  fof(f56,plain,(
% 7.71/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.71/1.48    inference(flattening,[],[f55])).
% 7.71/1.48  
% 7.71/1.48  fof(f90,plain,(
% 7.71/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f56])).
% 7.71/1.48  
% 7.71/1.48  fof(f115,plain,(
% 7.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.48    inference(equality_resolution,[],[f90])).
% 7.71/1.48  
% 7.71/1.48  fof(f21,axiom,(
% 7.71/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f46,plain,(
% 7.71/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.71/1.48    inference(ennf_transformation,[],[f21])).
% 7.71/1.48  
% 7.71/1.48  fof(f47,plain,(
% 7.71/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.71/1.48    inference(flattening,[],[f46])).
% 7.71/1.48  
% 7.71/1.48  fof(f92,plain,(
% 7.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f47])).
% 7.71/1.48  
% 7.71/1.48  fof(f93,plain,(
% 7.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f47])).
% 7.71/1.48  
% 7.71/1.48  fof(f94,plain,(
% 7.71/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f47])).
% 7.71/1.48  
% 7.71/1.48  fof(f4,axiom,(
% 7.71/1.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f27,plain,(
% 7.71/1.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.71/1.48    inference(ennf_transformation,[],[f4])).
% 7.71/1.48  
% 7.71/1.48  fof(f68,plain,(
% 7.71/1.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f27])).
% 7.71/1.48  
% 7.71/1.48  fof(f96,plain,(
% 7.71/1.48    ~v1_xboole_0(sK1)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f97,plain,(
% 7.71/1.48    ~v1_xboole_0(sK2)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f103,plain,(
% 7.71/1.48    v1_funct_2(sK4,sK2,sK1)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f99,plain,(
% 7.71/1.48    ~v1_xboole_0(sK3)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f106,plain,(
% 7.71/1.48    v1_funct_2(sK5,sK3,sK1)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f101,plain,(
% 7.71/1.48    r1_subset_1(sK2,sK3)),
% 7.71/1.48    inference(cnf_transformation,[],[f63])).
% 7.71/1.48  
% 7.71/1.48  fof(f14,axiom,(
% 7.71/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f34,plain,(
% 7.71/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.71/1.48    inference(ennf_transformation,[],[f14])).
% 7.71/1.48  
% 7.71/1.48  fof(f35,plain,(
% 7.71/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.71/1.48    inference(flattening,[],[f34])).
% 7.71/1.48  
% 7.71/1.48  fof(f53,plain,(
% 7.71/1.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.71/1.48    inference(nnf_transformation,[],[f35])).
% 7.71/1.48  
% 7.71/1.48  fof(f80,plain,(
% 7.71/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f53])).
% 7.71/1.48  
% 7.71/1.48  fof(f1,axiom,(
% 7.71/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f50,plain,(
% 7.71/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.71/1.48    inference(nnf_transformation,[],[f1])).
% 7.71/1.48  
% 7.71/1.48  fof(f64,plain,(
% 7.71/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f50])).
% 7.71/1.48  
% 7.71/1.48  fof(f110,plain,(
% 7.71/1.48    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.71/1.48    inference(definition_unfolding,[],[f64,f69])).
% 7.71/1.48  
% 7.71/1.48  fof(f15,axiom,(
% 7.71/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f36,plain,(
% 7.71/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.48    inference(ennf_transformation,[],[f15])).
% 7.71/1.48  
% 7.71/1.48  fof(f82,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.48    inference(cnf_transformation,[],[f36])).
% 7.71/1.48  
% 7.71/1.48  fof(f17,axiom,(
% 7.71/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f38,plain,(
% 7.71/1.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.71/1.48    inference(ennf_transformation,[],[f17])).
% 7.71/1.48  
% 7.71/1.48  fof(f39,plain,(
% 7.71/1.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.71/1.48    inference(flattening,[],[f38])).
% 7.71/1.48  
% 7.71/1.48  fof(f85,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f39])).
% 7.71/1.48  
% 7.71/1.48  fof(f18,axiom,(
% 7.71/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f40,plain,(
% 7.71/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.71/1.48    inference(ennf_transformation,[],[f18])).
% 7.71/1.48  
% 7.71/1.48  fof(f41,plain,(
% 7.71/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.71/1.48    inference(flattening,[],[f40])).
% 7.71/1.48  
% 7.71/1.48  fof(f54,plain,(
% 7.71/1.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.71/1.48    inference(nnf_transformation,[],[f41])).
% 7.71/1.48  
% 7.71/1.48  fof(f86,plain,(
% 7.71/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f54])).
% 7.71/1.48  
% 7.71/1.48  fof(f16,axiom,(
% 7.71/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f24,plain,(
% 7.71/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.71/1.48    inference(pure_predicate_removal,[],[f16])).
% 7.71/1.48  
% 7.71/1.48  fof(f37,plain,(
% 7.71/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.48    inference(ennf_transformation,[],[f24])).
% 7.71/1.48  
% 7.71/1.48  fof(f83,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.48    inference(cnf_transformation,[],[f37])).
% 7.71/1.48  
% 7.71/1.48  fof(f13,axiom,(
% 7.71/1.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f33,plain,(
% 7.71/1.48    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.71/1.48    inference(ennf_transformation,[],[f13])).
% 7.71/1.48  
% 7.71/1.48  fof(f52,plain,(
% 7.71/1.48    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.71/1.48    inference(nnf_transformation,[],[f33])).
% 7.71/1.48  
% 7.71/1.48  fof(f79,plain,(
% 7.71/1.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f52])).
% 7.71/1.48  
% 7.71/1.48  fof(f12,axiom,(
% 7.71/1.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f32,plain,(
% 7.71/1.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.71/1.48    inference(ennf_transformation,[],[f12])).
% 7.71/1.48  
% 7.71/1.48  fof(f77,plain,(
% 7.71/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f32])).
% 7.71/1.48  
% 7.71/1.48  fof(f11,axiom,(
% 7.71/1.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f75,plain,(
% 7.71/1.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.71/1.48    inference(cnf_transformation,[],[f11])).
% 7.71/1.48  
% 7.71/1.48  fof(f9,axiom,(
% 7.71/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f30,plain,(
% 7.71/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 7.71/1.48    inference(ennf_transformation,[],[f9])).
% 7.71/1.48  
% 7.71/1.48  fof(f73,plain,(
% 7.71/1.48    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 7.71/1.48    inference(cnf_transformation,[],[f30])).
% 7.71/1.48  
% 7.71/1.48  fof(f3,axiom,(
% 7.71/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.48  
% 7.71/1.48  fof(f67,plain,(
% 7.71/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.71/1.48    inference(cnf_transformation,[],[f3])).
% 7.71/1.48  
% 7.71/1.48  fof(f7,axiom,(
% 7.71/1.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.71/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f28,plain,(
% 7.71/1.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.71/1.49    inference(ennf_transformation,[],[f7])).
% 7.71/1.49  
% 7.71/1.49  fof(f70,plain,(
% 7.71/1.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f28])).
% 7.71/1.49  
% 7.71/1.49  fof(f76,plain,(
% 7.71/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.71/1.49    inference(cnf_transformation,[],[f11])).
% 7.71/1.49  
% 7.71/1.49  fof(f8,axiom,(
% 7.71/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.71/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f29,plain,(
% 7.71/1.49    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.71/1.49    inference(ennf_transformation,[],[f8])).
% 7.71/1.49  
% 7.71/1.49  fof(f51,plain,(
% 7.71/1.49    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.71/1.49    inference(nnf_transformation,[],[f29])).
% 7.71/1.49  
% 7.71/1.49  fof(f71,plain,(
% 7.71/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f51])).
% 7.71/1.49  
% 7.71/1.49  fof(f89,plain,(
% 7.71/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f56])).
% 7.71/1.49  
% 7.71/1.49  fof(f116,plain,(
% 7.71/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.71/1.49    inference(equality_resolution,[],[f89])).
% 7.71/1.49  
% 7.71/1.49  fof(f10,axiom,(
% 7.71/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.71/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.71/1.49  
% 7.71/1.49  fof(f31,plain,(
% 7.71/1.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.71/1.49    inference(ennf_transformation,[],[f10])).
% 7.71/1.49  
% 7.71/1.49  fof(f74,plain,(
% 7.71/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.71/1.49    inference(cnf_transformation,[],[f31])).
% 7.71/1.49  
% 7.71/1.49  fof(f108,plain,(
% 7.71/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.71/1.49    inference(cnf_transformation,[],[f63])).
% 7.71/1.49  
% 7.71/1.49  fof(f98,plain,(
% 7.71/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.71/1.49    inference(cnf_transformation,[],[f63])).
% 7.71/1.49  
% 7.71/1.49  cnf(c_38,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_757,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_38]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1801,plain,
% 7.71/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f111]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_790,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.71/1.49      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1771,plain,
% 7.71/1.49      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 7.71/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_790]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2627,plain,
% 7.71/1.49      ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1801,c_1771]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_31,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.71/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_764,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_31]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1794,plain,
% 7.71/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_23,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.71/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_770,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.71/1.49      | ~ v1_funct_1(X0_57)
% 7.71/1.49      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1789,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 7.71/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.71/1.49      | v1_funct_1(X2_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7091,plain,
% 7.71/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
% 7.71/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1794,c_1789]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_33,negated_conjecture,
% 7.71/1.49      ( v1_funct_1(sK5) ),
% 7.71/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2405,plain,
% 7.71/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.71/1.49      | ~ v1_funct_1(sK5)
% 7.71/1.49      | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_770]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2750,plain,
% 7.71/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.71/1.49      | ~ v1_funct_1(sK5)
% 7.71/1.49      | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_2405]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7353,plain,
% 7.71/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7091,c_33,c_31,c_2750]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_34,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.71/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_761,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_34]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1797,plain,
% 7.71/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7092,plain,
% 7.71/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
% 7.71/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1797,c_1789]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_36,negated_conjecture,
% 7.71/1.49      ( v1_funct_1(sK4) ),
% 7.71/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2410,plain,
% 7.71/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.71/1.49      | ~ v1_funct_1(sK4)
% 7.71/1.49      | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_770]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2755,plain,
% 7.71/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.71/1.49      | ~ v1_funct_1(sK4)
% 7.71/1.49      | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_2410]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7359,plain,
% 7.71/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7092,c_36,c_34,c_2755]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_25,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f115]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_29,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_28,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_27,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_441,plain,
% 7.71/1.49      ( ~ v1_funct_1(X3)
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_25,c_29,c_28,c_27]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_442,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | v1_xboole_0(X1)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_441]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_750,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.71/1.49      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.71/1.49      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.71/1.49      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.71/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.71/1.49      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.71/1.49      | ~ v1_funct_1(X0_57)
% 7.71/1.49      | ~ v1_funct_1(X3_57)
% 7.71/1.49      | v1_xboole_0(X1_57)
% 7.71/1.49      | v1_xboole_0(X2_57)
% 7.71/1.49      | v1_xboole_0(X4_57)
% 7.71/1.49      | v1_xboole_0(X5_57)
% 7.71/1.49      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_442]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1808,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 7.71/1.49      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.71/1.49      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.71/1.49      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.71/1.49      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.71/1.49      | v1_funct_1(X2_57) != iProver_top
% 7.71/1.49      | v1_funct_1(X5_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X3_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X4_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.71/1.49      | ~ v1_xboole_0(X1)
% 7.71/1.49      | v1_xboole_0(X0) ),
% 7.71/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_788,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.71/1.49      | ~ v1_xboole_0(X1_57)
% 7.71/1.49      | v1_xboole_0(X0_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1773,plain,
% 7.71/1.49      ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
% 7.71/1.49      | v1_xboole_0(X1_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2083,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X4_57) = X5_57
% 7.71/1.49      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.71/1.49      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.71/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.71/1.49      | v1_funct_1(X5_57) != iProver_top
% 7.71/1.49      | v1_funct_1(X2_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X4_57) = iProver_top ),
% 7.71/1.49      inference(forward_subsumption_resolution,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_1808,c_1773]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13884,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.71/1.49      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.71/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.71/1.49      | v1_funct_1(sK4) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7359,c_2083]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_42,negated_conjecture,
% 7.71/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_45,plain,
% 7.71/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_41,negated_conjecture,
% 7.71/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.71/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_46,plain,
% 7.71/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_51,plain,
% 7.71/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_35,negated_conjecture,
% 7.71/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_52,plain,
% 7.71/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_53,plain,
% 7.71/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18122,plain,
% 7.71/1.49      ( v1_funct_1(X1_57) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.71/1.49      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.71/1.49      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_13884,c_45,c_46,c_51,c_52,c_53]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18123,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.71/1.49      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_18122]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18136,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.71/1.49      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.71/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.71/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 7.71/1.49      | v1_funct_1(sK5) != iProver_top
% 7.71/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7353,c_18123]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_39,negated_conjecture,
% 7.71/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.71/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_48,plain,
% 7.71/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_54,plain,
% 7.71/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_32,negated_conjecture,
% 7.71/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_55,plain,
% 7.71/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_56,plain,
% 7.71/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18474,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.71/1.49      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_18136,c_48,c_54,c_55,c_56]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18484,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.71/1.49      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2627,c_18474]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_37,negated_conjecture,
% 7.71/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.71/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_758,negated_conjecture,
% 7.71/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_37]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1800,plain,
% 7.71/1.49      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_16,plain,
% 7.71/1.49      ( ~ r1_subset_1(X0,X1)
% 7.71/1.49      | r1_xboole_0(X0,X1)
% 7.71/1.49      | v1_xboole_0(X0)
% 7.71/1.49      | v1_xboole_0(X1) ),
% 7.71/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_776,plain,
% 7.71/1.49      ( ~ r1_subset_1(X0_57,X1_57)
% 7.71/1.49      | r1_xboole_0(X0_57,X1_57)
% 7.71/1.49      | v1_xboole_0(X1_57)
% 7.71/1.49      | v1_xboole_0(X0_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1783,plain,
% 7.71/1.49      ( r1_subset_1(X0_57,X1_57) != iProver_top
% 7.71/1.49      | r1_xboole_0(X0_57,X1_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_776]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4397,plain,
% 7.71/1.49      ( r1_xboole_0(sK2,sK3) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1800,c_1783]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_50,plain,
% 7.71/1.49      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2315,plain,
% 7.71/1.49      ( ~ r1_subset_1(sK2,sK3)
% 7.71/1.49      | r1_xboole_0(sK2,sK3)
% 7.71/1.49      | v1_xboole_0(sK3)
% 7.71/1.49      | v1_xboole_0(sK2) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_776]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2316,plain,
% 7.71/1.49      ( r1_subset_1(sK2,sK3) != iProver_top
% 7.71/1.49      | r1_xboole_0(sK2,sK3) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_2315]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4780,plain,
% 7.71/1.49      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_4397,c_46,c_48,c_50,c_2316]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1,plain,
% 7.71/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.71/1.49      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f110]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_791,plain,
% 7.71/1.49      ( ~ r1_xboole_0(X0_57,X1_57)
% 7.71/1.49      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1770,plain,
% 7.71/1.49      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_791]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4786,plain,
% 7.71/1.49      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4780,c_1770]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18485,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.71/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_18484,c_4786]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18486,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.71/1.49      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_18485,c_2627]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_17,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | v1_relat_1(X0) ),
% 7.71/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_775,plain,
% 7.71/1.49      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.71/1.49      | v1_relat_1(X0_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1784,plain,
% 7.71/1.49      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3496,plain,
% 7.71/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1797,c_1784]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_19,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | v1_partfun1(X0,X1)
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | v1_xboole_0(X2) ),
% 7.71/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_773,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.71/1.49      | v1_partfun1(X0_57,X1_57)
% 7.71/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.71/1.49      | ~ v1_funct_1(X0_57)
% 7.71/1.49      | v1_xboole_0(X2_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1786,plain,
% 7.71/1.49      ( v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.71/1.49      | v1_partfun1(X0_57,X1_57) = iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.71/1.49      | v1_funct_1(X0_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X2_57) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5514,plain,
% 7.71/1.49      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.71/1.49      | v1_partfun1(sK4,sK2) = iProver_top
% 7.71/1.49      | v1_funct_1(sK4) != iProver_top
% 7.71/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1797,c_1786]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2430,plain,
% 7.71/1.49      ( ~ v1_funct_2(sK4,X0_57,X1_57)
% 7.71/1.49      | v1_partfun1(sK4,X0_57)
% 7.71/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.71/1.49      | ~ v1_funct_1(sK4)
% 7.71/1.49      | v1_xboole_0(X1_57) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_773]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2804,plain,
% 7.71/1.49      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.71/1.49      | v1_partfun1(sK4,sK2)
% 7.71/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.71/1.49      | ~ v1_funct_1(sK4)
% 7.71/1.49      | v1_xboole_0(sK1) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_2430]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2805,plain,
% 7.71/1.49      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.71/1.49      | v1_partfun1(sK4,sK2) = iProver_top
% 7.71/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.71/1.49      | v1_funct_1(sK4) != iProver_top
% 7.71/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_2804]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_6217,plain,
% 7.71/1.49      ( v1_partfun1(sK4,sK2) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_5514,c_45,c_51,c_52,c_53,c_2805]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_22,plain,
% 7.71/1.49      ( ~ v1_partfun1(X0,X1)
% 7.71/1.49      | ~ v4_relat_1(X0,X1)
% 7.71/1.49      | ~ v1_relat_1(X0)
% 7.71/1.49      | k1_relat_1(X0) = X1 ),
% 7.71/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_771,plain,
% 7.71/1.49      ( ~ v1_partfun1(X0_57,X1_57)
% 7.71/1.49      | ~ v4_relat_1(X0_57,X1_57)
% 7.71/1.49      | ~ v1_relat_1(X0_57)
% 7.71/1.49      | k1_relat_1(X0_57) = X1_57 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1788,plain,
% 7.71/1.49      ( k1_relat_1(X0_57) = X1_57
% 7.71/1.49      | v1_partfun1(X0_57,X1_57) != iProver_top
% 7.71/1.49      | v4_relat_1(X0_57,X1_57) != iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7156,plain,
% 7.71/1.49      ( k1_relat_1(sK4) = sK2
% 7.71/1.49      | v4_relat_1(sK4,sK2) != iProver_top
% 7.71/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_6217,c_1788]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2268,plain,
% 7.71/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.71/1.49      | v1_relat_1(sK4) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_775]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18,plain,
% 7.71/1.49      ( v4_relat_1(X0,X1)
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.71/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_774,plain,
% 7.71/1.49      ( v4_relat_1(X0_57,X1_57)
% 7.71/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2310,plain,
% 7.71/1.49      ( v4_relat_1(sK4,sK2)
% 7.71/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_774]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2542,plain,
% 7.71/1.49      ( ~ v1_partfun1(sK4,X0_57)
% 7.71/1.49      | ~ v4_relat_1(sK4,X0_57)
% 7.71/1.49      | ~ v1_relat_1(sK4)
% 7.71/1.49      | k1_relat_1(sK4) = X0_57 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_771]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2557,plain,
% 7.71/1.49      ( ~ v1_partfun1(sK4,sK2)
% 7.71/1.49      | ~ v4_relat_1(sK4,sK2)
% 7.71/1.49      | ~ v1_relat_1(sK4)
% 7.71/1.49      | k1_relat_1(sK4) = sK2 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_2542]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7498,plain,
% 7.71/1.49      ( k1_relat_1(sK4) = sK2 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7156,c_42,c_36,c_35,c_34,c_2268,c_2310,c_2557,c_2804]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13,plain,
% 7.71/1.49      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.71/1.49      | ~ v1_relat_1(X0)
% 7.71/1.49      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_779,plain,
% 7.71/1.49      ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.71/1.49      | ~ v1_relat_1(X0_57)
% 7.71/1.49      | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_13]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1780,plain,
% 7.71/1.49      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7511,plain,
% 7.71/1.49      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(sK2,X0_57) != iProver_top
% 7.71/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7498,c_1780]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2269,plain,
% 7.71/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.71/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_2268]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7793,plain,
% 7.71/1.49      ( r1_xboole_0(sK2,X0_57) != iProver_top
% 7.71/1.49      | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7511,c_53,c_2269]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7794,plain,
% 7.71/1.49      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(sK2,X0_57) != iProver_top ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_7793]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7801,plain,
% 7.71/1.49      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4780,c_7794]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_12,plain,
% 7.71/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.71/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_780,plain,
% 7.71/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57)
% 7.71/1.49      | ~ v1_relat_1(X0_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_12]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1779,plain,
% 7.71/1.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0_57,X1_57)),X1_57) = iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8181,plain,
% 7.71/1.49      ( r1_tarski(k1_relat_1(k1_xboole_0),sK3) = iProver_top
% 7.71/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7801,c_1779]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_11,plain,
% 7.71/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_781,plain,
% 7.71/1.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8184,plain,
% 7.71/1.49      ( r1_tarski(k1_xboole_0,sK3) = iProver_top
% 7.71/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_8181,c_781]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8922,plain,
% 7.71/1.49      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_8184,c_53,c_2269]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8,plain,
% 7.71/1.49      ( ~ r1_tarski(X0,X1)
% 7.71/1.49      | ~ v1_relat_1(X2)
% 7.71/1.49      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 7.71/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_784,plain,
% 7.71/1.49      ( ~ r1_tarski(X0_57,X1_57)
% 7.71/1.49      | ~ v1_relat_1(X2_57)
% 7.71/1.49      | k9_relat_1(k7_relat_1(X2_57,X1_57),X0_57) = k9_relat_1(X2_57,X0_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1777,plain,
% 7.71/1.49      ( k9_relat_1(k7_relat_1(X0_57,X1_57),X2_57) = k9_relat_1(X0_57,X2_57)
% 7.71/1.49      | r1_tarski(X2_57,X1_57) != iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8927,plain,
% 7.71/1.49      ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_8922,c_1777]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9096,plain,
% 7.71/1.49      ( k9_relat_1(k7_relat_1(sK4,sK3),k1_xboole_0) = k9_relat_1(sK4,k1_xboole_0) ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_3496,c_8927]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3,plain,
% 7.71/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_789,plain,
% 7.71/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_57)) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1772,plain,
% 7.71/1.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_57)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_789]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3497,plain,
% 7.71/1.49      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1772,c_1784]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5,plain,
% 7.71/1.49      ( ~ v1_relat_1(X0)
% 7.71/1.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.71/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_787,plain,
% 7.71/1.49      ( ~ v1_relat_1(X0_57)
% 7.71/1.49      | k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1774,plain,
% 7.71/1.49      ( k9_relat_1(X0_57,k1_relat_1(X0_57)) = k2_relat_1(X0_57)
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4390,plain,
% 7.71/1.49      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_3497,c_1774]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10,plain,
% 7.71/1.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_782,plain,
% 7.71/1.49      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4391,plain,
% 7.71/1.49      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_4390,c_781,c_782]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9102,plain,
% 7.71/1.49      ( k9_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_9096,c_4391,c_7801]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7,plain,
% 7.71/1.49      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.71/1.49      | ~ v1_relat_1(X0)
% 7.71/1.49      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_785,plain,
% 7.71/1.49      ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.71/1.49      | ~ v1_relat_1(X0_57)
% 7.71/1.49      | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1776,plain,
% 7.71/1.49      ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
% 7.71/1.49      | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_785]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9278,plain,
% 7.71/1.49      ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0) = iProver_top
% 7.71/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_9102,c_1776]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9279,plain,
% 7.71/1.49      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top
% 7.71/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_9278,c_7498]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9473,plain,
% 7.71/1.49      ( r1_xboole_0(sK2,k1_xboole_0) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_9279,c_53,c_2269]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9482,plain,
% 7.71/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_9473,c_7794]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_18487,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.71/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_18486,c_4786,c_9482]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_26,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.71/1.49      inference(cnf_transformation,[],[f116]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_432,plain,
% 7.71/1.49      ( ~ v1_funct_1(X3)
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X1)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_26,c_29,c_28,c_27]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_433,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.71/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.71/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.49      | ~ v1_funct_1(X0)
% 7.71/1.49      | ~ v1_funct_1(X3)
% 7.71/1.49      | v1_xboole_0(X1)
% 7.71/1.49      | v1_xboole_0(X2)
% 7.71/1.49      | v1_xboole_0(X4)
% 7.71/1.49      | v1_xboole_0(X5)
% 7.71/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_432]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_751,plain,
% 7.71/1.49      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.71/1.49      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.71/1.49      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.71/1.49      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.71/1.49      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.71/1.49      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.71/1.49      | ~ v1_funct_1(X0_57)
% 7.71/1.49      | ~ v1_funct_1(X3_57)
% 7.71/1.49      | v1_xboole_0(X1_57)
% 7.71/1.49      | v1_xboole_0(X2_57)
% 7.71/1.49      | v1_xboole_0(X4_57)
% 7.71/1.49      | v1_xboole_0(X5_57)
% 7.71/1.49      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_433]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1807,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 7.71/1.49      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.71/1.49      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.71/1.49      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.71/1.49      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.71/1.49      | v1_funct_1(X2_57) != iProver_top
% 7.71/1.49      | v1_funct_1(X5_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X3_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X4_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2055,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X0_57) = X2_57
% 7.71/1.49      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.71/1.49      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.71/1.49      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.71/1.49      | v1_funct_1(X5_57) != iProver_top
% 7.71/1.49      | v1_funct_1(X2_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X1_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(X4_57) = iProver_top ),
% 7.71/1.49      inference(forward_subsumption_resolution,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_1807,c_1773]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_11714,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 7.71/1.49      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.71/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.71/1.49      | v1_funct_1(sK4) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.71/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7359,c_2055]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13655,plain,
% 7.71/1.49      ( v1_funct_1(X1_57) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.71/1.49      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 7.71/1.49      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_11714,c_45,c_46,c_51,c_52,c_53]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13656,plain,
% 7.71/1.49      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.71/1.49      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 7.71/1.49      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.71/1.49      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.71/1.49      | v1_funct_1(X1_57) != iProver_top
% 7.71/1.49      | v1_xboole_0(X0_57) = iProver_top ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_13655]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_13669,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.71/1.49      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.71/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.71/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 7.71/1.49      | v1_funct_1(sK5) != iProver_top
% 7.71/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7353,c_13656]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14785,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.71/1.49      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_13669,c_48,c_54,c_55,c_56]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14795,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.71/1.49      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_2627,c_14785]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14796,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.71/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_14795,c_4786]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14797,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.71/1.49      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_14796,c_2627]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_14798,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.71/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.71/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.71/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_14797,c_4786,c_9482]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3495,plain,
% 7.71/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1794,c_1784]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5513,plain,
% 7.71/1.49      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.71/1.49      | v1_partfun1(sK5,sK3) = iProver_top
% 7.71/1.49      | v1_funct_1(sK5) != iProver_top
% 7.71/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_1794,c_1786]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2425,plain,
% 7.71/1.49      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 7.71/1.49      | v1_partfun1(sK5,X0_57)
% 7.71/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.71/1.49      | ~ v1_funct_1(sK5)
% 7.71/1.49      | v1_xboole_0(X1_57) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_773]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2801,plain,
% 7.71/1.49      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.71/1.49      | v1_partfun1(sK5,sK3)
% 7.71/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.71/1.49      | ~ v1_funct_1(sK5)
% 7.71/1.49      | v1_xboole_0(sK1) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_2425]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2802,plain,
% 7.71/1.49      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.71/1.49      | v1_partfun1(sK5,sK3) = iProver_top
% 7.71/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.71/1.49      | v1_funct_1(sK5) != iProver_top
% 7.71/1.49      | v1_xboole_0(sK1) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_2801]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_5930,plain,
% 7.71/1.49      ( v1_partfun1(sK5,sK3) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_5513,c_45,c_54,c_55,c_56,c_2802]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7157,plain,
% 7.71/1.49      ( k1_relat_1(sK5) = sK3
% 7.71/1.49      | v4_relat_1(sK5,sK3) != iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_5930,c_1788]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2265,plain,
% 7.71/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.71/1.49      | v1_relat_1(sK5) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_775]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2307,plain,
% 7.71/1.49      ( v4_relat_1(sK5,sK3)
% 7.71/1.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_774]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2514,plain,
% 7.71/1.49      ( ~ v1_partfun1(sK5,X0_57)
% 7.71/1.49      | ~ v4_relat_1(sK5,X0_57)
% 7.71/1.49      | ~ v1_relat_1(sK5)
% 7.71/1.49      | k1_relat_1(sK5) = X0_57 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_771]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_3198,plain,
% 7.71/1.49      ( ~ v1_partfun1(sK5,sK3)
% 7.71/1.49      | ~ v4_relat_1(sK5,sK3)
% 7.71/1.49      | ~ v1_relat_1(sK5)
% 7.71/1.49      | k1_relat_1(sK5) = sK3 ),
% 7.71/1.49      inference(instantiation,[status(thm)],[c_2514]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7544,plain,
% 7.71/1.49      ( k1_relat_1(sK5) = sK3 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7157,c_42,c_33,c_32,c_31,c_2265,c_2307,c_2801,c_3198]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9,plain,
% 7.71/1.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.71/1.49      | ~ v1_relat_1(X1)
% 7.71/1.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.71/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_783,plain,
% 7.71/1.49      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 7.71/1.49      | ~ v1_relat_1(X1_57)
% 7.71/1.49      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_1778,plain,
% 7.71/1.49      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7558,plain,
% 7.71/1.49      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(X0_57,sK3) != iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7544,c_1778]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2266,plain,
% 7.71/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.71/1.49      | v1_relat_1(sK5) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_2265]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8453,plain,
% 7.71/1.49      ( r1_xboole_0(X0_57,sK3) != iProver_top
% 7.71/1.49      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7558,c_56,c_2266]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8454,plain,
% 7.71/1.49      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(X0_57,sK3) != iProver_top ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_8453]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8461,plain,
% 7.71/1.49      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_4780,c_8454]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8535,plain,
% 7.71/1.49      ( r1_tarski(k1_relat_1(k1_xboole_0),sK2) = iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_8461,c_1779]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8538,plain,
% 7.71/1.49      ( r1_tarski(k1_xboole_0,sK2) = iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_8535,c_781]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8932,plain,
% 7.71/1.49      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_8538,c_56,c_2266]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8937,plain,
% 7.71/1.49      ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_xboole_0) = k9_relat_1(X0_57,k1_xboole_0)
% 7.71/1.49      | v1_relat_1(X0_57) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_8932,c_1777]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10946,plain,
% 7.71/1.49      ( k9_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_3495,c_8937]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10955,plain,
% 7.71/1.49      ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(light_normalisation,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_10946,c_4391,c_8461]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10978,plain,
% 7.71/1.49      ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_10955,c_1776]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_10979,plain,
% 7.71/1.49      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(light_normalisation,[status(thm)],[c_10978,c_7544]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_11456,plain,
% 7.71/1.49      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_10979,c_56,c_2266]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7557,plain,
% 7.71/1.49      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(sK3,X0_57) != iProver_top
% 7.71/1.49      | v1_relat_1(sK5) != iProver_top ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_7544,c_1780]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8171,plain,
% 7.71/1.49      ( r1_xboole_0(sK3,X0_57) != iProver_top
% 7.71/1.49      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 7.71/1.49      inference(global_propositional_subsumption,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_7557,c_56,c_2266]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_8172,plain,
% 7.71/1.49      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.71/1.49      | r1_xboole_0(sK3,X0_57) != iProver_top ),
% 7.71/1.49      inference(renaming,[status(thm)],[c_8171]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_11465,plain,
% 7.71/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.71/1.49      inference(superposition,[status(thm)],[c_11456,c_8172]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_30,negated_conjecture,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_765,negated_conjecture,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.71/1.49      inference(subtyping,[status(esa)],[c_30]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_2888,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_2627,c_765]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_4790,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_4786,c_2888]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7357,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_7353,c_4790]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_7646,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_7357,c_7359]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_9889,plain,
% 7.71/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.71/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.71/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 7.71/1.49      inference(demodulation,[status(thm)],[c_9482,c_7646]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_49,plain,
% 7.71/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_40,negated_conjecture,
% 7.71/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.71/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(c_47,plain,
% 7.71/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.71/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.71/1.49  
% 7.71/1.49  cnf(contradiction,plain,
% 7.71/1.49      ( $false ),
% 7.71/1.49      inference(minisat,
% 7.71/1.49                [status(thm)],
% 7.71/1.49                [c_18487,c_14798,c_11465,c_9889,c_49,c_47]) ).
% 7.71/1.49  
% 7.71/1.49  
% 7.71/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.49  
% 7.71/1.49  ------                               Statistics
% 7.71/1.49  
% 7.71/1.49  ------ Selected
% 7.71/1.49  
% 7.71/1.49  total_time:                             0.671
% 7.71/1.49  
%------------------------------------------------------------------------------
