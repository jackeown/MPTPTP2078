%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:28 EST 2020

% Result     : Theorem 11.64s
% Output     : CNFRefutation 11.64s
% Verified   : 
% Statistics : Number of formulae       :  299 (21209 expanded)
%              Number of clauses        :  198 (5725 expanded)
%              Number of leaves         :   26 (7855 expanded)
%              Depth                    :   30
%              Number of atoms          : 1361 (252189 expanded)
%              Number of equality atoms :  535 (57492 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

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

fof(f99,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f97,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f100,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

fof(f101,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f75,f67])).

fof(f105,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f63])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f106,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f88,plain,(
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

fof(f113,plain,(
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
    inference(equality_resolution,[],[f88])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

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

fof(f90,plain,(
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

fof(f91,plain,(
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

fof(f92,plain,(
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

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f63])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f67])).

fof(f87,plain,(
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

fof(f114,plain,(
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
    inference(equality_resolution,[],[f87])).

cnf(c_35,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_571,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1340,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_14,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_589,plain,
    ( ~ r1_subset_1(X0_56,X1_56)
    | r1_xboole_0(X0_56,X1_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1323,plain,
    ( r1_subset_1(X0_56,X1_56) != iProver_top
    | r1_xboole_0(X0_56,X1_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_589])).

cnf(c_3939,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1323])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_44,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_46,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_48,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1852,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_589])).

cnf(c_1853,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1852])).

cnf(c_4347,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3939,c_44,c_46,c_48,c_1853])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_574,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1337,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_586,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | v1_partfun1(X0_56,X1_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | v1_xboole_0(X2_56) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1326,plain,
    ( v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
    | v1_partfun1(X0_56,X1_56) = iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(X2_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_4979,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1326])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_43,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_49,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_50,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1958,plain,
    ( ~ v1_funct_2(sK4,X0_56,X1_56)
    | v1_partfun1(sK4,X0_56)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_56) ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_2327,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1958])).

cnf(c_2328,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2327])).

cnf(c_5735,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4979,c_43,c_49,c_50,c_51,c_2328])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_584,plain,
    ( ~ v1_partfun1(X0_56,X1_56)
    | ~ v4_relat_1(X0_56,X1_56)
    | ~ v1_relat_1(X0_56)
    | k1_relat_1(X0_56) = X1_56 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1328,plain,
    ( k1_relat_1(X0_56) = X1_56
    | v1_partfun1(X0_56,X1_56) != iProver_top
    | v4_relat_1(X0_56,X1_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_584])).

cnf(c_5740,plain,
    ( k1_relat_1(sK4) = sK2
    | v4_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5735,c_1328])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1805,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_587,plain,
    ( v4_relat_1(X0_56,X1_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1831,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_2086,plain,
    ( ~ v1_partfun1(sK4,X0_56)
    | ~ v4_relat_1(sK4,X0_56)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0_56 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_2119,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_6193,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5740,c_40,c_34,c_33,c_32,c_1805,c_1831,c_2119,c_2327])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_592,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_56),X1_56)
    | ~ v1_relat_1(X0_56)
    | k7_relat_1(X0_56,X1_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1320,plain,
    ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_56),X1_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_6219,plain,
    ( k7_relat_1(sK4,X0_56) = k1_xboole_0
    | r1_xboole_0(sK2,X0_56) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6193,c_1320])).

cnf(c_1806,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1805])).

cnf(c_7475,plain,
    ( r1_xboole_0(sK2,X0_56) != iProver_top
    | k7_relat_1(sK4,X0_56) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6219,c_51,c_1806])).

cnf(c_7476,plain,
    ( k7_relat_1(sK4,X0_56) = k1_xboole_0
    | r1_xboole_0(sK2,X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_7475])).

cnf(c_7483,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4347,c_7476])).

cnf(c_1324,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | v1_relat_1(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_2587,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1324])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_600,plain,
    ( ~ v1_relat_1(X0_56)
    | k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1312,plain,
    ( k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_2746,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0_56)) = k9_relat_1(sK4,X0_56) ),
    inference(superposition,[status(thm)],[c_2587,c_1312])).

cnf(c_7648,plain,
    ( k9_relat_1(sK4,sK3) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7483,c_2746])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_599,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_56),X1_56)
    | ~ v1_relat_1(X0_56)
    | k9_relat_1(X0_56,X1_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1313,plain,
    ( k9_relat_1(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_56),X1_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_6221,plain,
    ( k9_relat_1(sK4,X0_56) = k1_xboole_0
    | r1_xboole_0(sK2,X0_56) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6193,c_1313])).

cnf(c_7636,plain,
    ( r1_xboole_0(sK2,X0_56) != iProver_top
    | k9_relat_1(sK4,X0_56) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6221,c_51,c_1806])).

cnf(c_7637,plain,
    ( k9_relat_1(sK4,X0_56) = k1_xboole_0
    | r1_xboole_0(sK2,X0_56) != iProver_top ),
    inference(renaming,[status(thm)],[c_7636])).

cnf(c_7644,plain,
    ( k9_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4347,c_7637])).

cnf(c_7865,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7648,c_7644])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_595,plain,
    ( ~ v1_relat_1(X0_56)
    | k1_relat_1(X0_56) = k1_xboole_0
    | k2_relat_1(X0_56) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1317,plain,
    ( k1_relat_1(X0_56) = k1_xboole_0
    | k2_relat_1(X0_56) != k1_xboole_0
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_7868,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7865,c_1317])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_602,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_56)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1809,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_2274,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_595])).

cnf(c_8385,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7868,c_1808,c_1809,c_2274,c_7865])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_593,plain,
    ( ~ v1_relat_1(X0_56)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56)) = k1_relat_1(k7_relat_1(X0_56,X1_56)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1319,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56)) = k1_relat_1(k7_relat_1(X0_56,X1_56))
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_3283,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_56)) = k1_relat_1(k7_relat_1(sK4,X0_56)) ),
    inference(superposition,[status(thm)],[c_2587,c_1319])).

cnf(c_6198,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0_56)) = k1_setfam_1(k2_tarski(sK2,X0_56)) ),
    inference(demodulation,[status(thm)],[c_6193,c_3283])).

cnf(c_7647,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7483,c_6198])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_577,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1334,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_583,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | k2_partfun1(X1_56,X2_56,X0_56,X3_56) = k7_relat_1(X0_56,X3_56) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1329,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,X3_56) = k7_relat_1(X2_56,X3_56)
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_583])).

cnf(c_5122,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1329])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1943,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_56,X1_56,sK5,X2_56) = k7_relat_1(sK5,X2_56) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_2314,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_5316,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5122,c_31,c_29,c_2314])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_570,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1341,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | k9_subset_1(X1_56,X2_56,X0_56) = k1_setfam_1(k2_tarski(X2_56,X0_56)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1309,plain,
    ( k9_subset_1(X0_56,X1_56,X2_56) = k1_setfam_1(k2_tarski(X1_56,X2_56))
    | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_603])).

cnf(c_2138,plain,
    ( k1_setfam_1(k2_tarski(X0_56,sK3)) = k9_subset_1(sK0,X0_56,sK3) ),
    inference(superposition,[status(thm)],[c_1341,c_1309])).

cnf(c_28,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_578,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_2342,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2138,c_578])).

cnf(c_5320,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_5316,c_2342])).

cnf(c_5123,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1329])).

cnf(c_1948,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_56,X1_56,sK4,X2_56) = k7_relat_1(sK4,X2_56) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_2319,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(instantiation,[status(thm)],[c_1948])).

cnf(c_5513,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5123,c_34,c_32,c_2319])).

cnf(c_5517,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_5320,c_5513])).

cnf(c_7887,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) != k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_7647,c_5517])).

cnf(c_8388,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8385,c_7887])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

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
    inference(cnf_transformation,[],[f113])).

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
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f91])).

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
    inference(cnf_transformation,[],[f92])).

cnf(c_336,plain,
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

cnf(c_337,plain,
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
    inference(renaming,[status(thm)],[c_336])).

cnf(c_564,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56)
    | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
    | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X1_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_337])).

cnf(c_1347,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
    | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X0_56) = X2_56
    | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
    | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_xboole_0(X3_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_564])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_601,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_xboole_0(X1_56)
    | v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1311,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
    | v1_xboole_0(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_1593,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X0_56,X4_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X0_56,X4_56))
    | k2_partfun1(k4_subset_1(X3_56,X0_56,X4_56),X1_56,k1_tmap_1(X3_56,X1_56,X0_56,X4_56,X2_56,X5_56),X4_56) = X5_56
    | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
    | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1347,c_1311])).

cnf(c_9623,plain,
    ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_1593])).

cnf(c_10990,plain,
    ( v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
    | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9623,c_43,c_44,c_49,c_50,c_51])).

cnf(c_10991,plain,
    ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_10990])).

cnf(c_11004,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5316,c_10991])).

cnf(c_52,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_53,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_54,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12404,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11004,c_46,c_52,c_53,c_54])).

cnf(c_12414,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_12404])).

cnf(c_8389,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8385,c_7647])).

cnf(c_4978,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1326])).

cnf(c_1953,plain,
    ( ~ v1_funct_2(sK5,X0_56,X1_56)
    | v1_partfun1(sK5,X0_56)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_56) ),
    inference(instantiation,[status(thm)],[c_586])).

cnf(c_2324,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1953])).

cnf(c_2325,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_5727,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4978,c_43,c_52,c_53,c_54,c_2325])).

cnf(c_5732,plain,
    ( k1_relat_1(sK5) = sK3
    | v4_relat_1(sK5,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5727,c_1328])).

cnf(c_1802,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_1828,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(instantiation,[status(thm)],[c_587])).

cnf(c_2050,plain,
    ( ~ v1_partfun1(sK5,X0_56)
    | ~ v4_relat_1(sK5,X0_56)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = X0_56 ),
    inference(instantiation,[status(thm)],[c_584])).

cnf(c_2718,plain,
    ( ~ v1_partfun1(sK5,sK3)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2050])).

cnf(c_6124,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5732,c_40,c_31,c_30,c_29,c_1802,c_1828,c_2324,c_2718])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_597,plain,
    ( ~ r1_xboole_0(X0_56,k1_relat_1(X1_56))
    | ~ v1_relat_1(X1_56)
    | k7_relat_1(X1_56,X0_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1315,plain,
    ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(X1_56,k1_relat_1(X0_56)) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_597])).

cnf(c_6151,plain,
    ( k7_relat_1(sK5,X0_56) = k1_xboole_0
    | r1_xboole_0(X0_56,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6124,c_1315])).

cnf(c_1803,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1802])).

cnf(c_7124,plain,
    ( r1_xboole_0(X0_56,sK3) != iProver_top
    | k7_relat_1(sK5,X0_56) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6151,c_54,c_1803])).

cnf(c_7125,plain,
    ( k7_relat_1(sK5,X0_56) = k1_xboole_0
    | r1_xboole_0(X0_56,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7124])).

cnf(c_7132,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4347,c_7125])).

cnf(c_2586,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1324])).

cnf(c_3282,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_56)) = k1_relat_1(k7_relat_1(sK5,X0_56)) ),
    inference(superposition,[status(thm)],[c_2586,c_1319])).

cnf(c_6129,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0_56)) = k1_setfam_1(k2_tarski(sK3,X0_56)) ),
    inference(demodulation,[status(thm)],[c_6124,c_3282])).

cnf(c_7135,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7132,c_6129])).

cnf(c_8390,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8385,c_7135])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_596,plain,
    ( ~ v1_relat_1(X0_56)
    | k7_relat_1(X0_56,k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56))) = k7_relat_1(X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1316,plain,
    ( k7_relat_1(X0_56,k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56))) = k7_relat_1(X0_56,X1_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_3293,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_56))) = k7_relat_1(sK5,X0_56) ),
    inference(superposition,[status(thm)],[c_2586,c_1316])).

cnf(c_3576,plain,
    ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0_56))) = k7_relat_1(sK5,X0_56) ),
    inference(light_normalisation,[status(thm)],[c_3293,c_3282])).

cnf(c_6401,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,X0_56))) = k7_relat_1(sK5,X0_56) ),
    inference(demodulation,[status(thm)],[c_6129,c_3576])).

cnf(c_9177,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_8390,c_6401])).

cnf(c_9191,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9177,c_7132])).

cnf(c_12415,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12414,c_8389,c_9191])).

cnf(c_12416,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12415,c_2138])).

cnf(c_12417,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12416,c_8389])).

cnf(c_12418,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12417])).

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
    inference(cnf_transformation,[],[f114])).

cnf(c_345,plain,
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

cnf(c_346,plain,
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
    inference(renaming,[status(thm)],[c_345])).

cnf(c_563,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56)
    | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
    | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X4_56) = X3_56 ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1348,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
    | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X4_56) = X5_56
    | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
    | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_xboole_0(X3_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_1621,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X0_56,X4_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X0_56,X4_56))
    | k2_partfun1(k4_subset_1(X3_56,X0_56,X4_56),X1_56,k1_tmap_1(X3_56,X1_56,X0_56,X4_56,X2_56,X5_56),X0_56) = X2_56
    | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
    | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
    | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X5_56) != iProver_top
    | v1_funct_1(X2_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(X1_56) = iProver_top
    | v1_xboole_0(X4_56) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1348,c_1311])).

cnf(c_11247,plain,
    ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5513,c_1621])).

cnf(c_14578,plain,
    ( v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
    | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11247,c_43,c_44,c_49,c_50,c_51])).

cnf(c_14579,plain,
    ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_14578])).

cnf(c_14592,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5316,c_14579])).

cnf(c_17702,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14592,c_46,c_52,c_53,c_54])).

cnf(c_17712,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2138,c_17702])).

cnf(c_17713,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17712,c_8389,c_9191])).

cnf(c_17714,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17713,c_2138])).

cnf(c_17715,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17714,c_8389])).

cnf(c_17716,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_17715])).

cnf(c_3294,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_56))) = k7_relat_1(sK4,X0_56) ),
    inference(superposition,[status(thm)],[c_2587,c_1316])).

cnf(c_3749,plain,
    ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0_56))) = k7_relat_1(sK4,X0_56) ),
    inference(light_normalisation,[status(thm)],[c_3294,c_3283])).

cnf(c_6819,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,X0_56))) = k7_relat_1(sK4,X0_56) ),
    inference(demodulation,[status(thm)],[c_6198,c_3749])).

cnf(c_25985,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK4,sK3) ),
    inference(superposition,[status(thm)],[c_8389,c_6819])).

cnf(c_26003,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_25985,c_7483])).

cnf(c_36319,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8388,c_38,c_36,c_12418,c_17716,c_26003])).

cnf(c_36321,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_36319,c_9191])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36321,c_26003])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:18:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.64/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.64/2.00  
% 11.64/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.64/2.00  
% 11.64/2.00  ------  iProver source info
% 11.64/2.00  
% 11.64/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.64/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.64/2.00  git: non_committed_changes: false
% 11.64/2.00  git: last_make_outside_of_git: false
% 11.64/2.00  
% 11.64/2.00  ------ 
% 11.64/2.00  ------ Parsing...
% 11.64/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.64/2.00  
% 11.64/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.64/2.00  
% 11.64/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.64/2.00  
% 11.64/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.64/2.00  ------ Proving...
% 11.64/2.00  ------ Problem Properties 
% 11.64/2.00  
% 11.64/2.00  
% 11.64/2.00  clauses                                 41
% 11.64/2.00  conjectures                             14
% 11.64/2.00  EPR                                     11
% 11.64/2.00  Horn                                    32
% 11.64/2.00  unary                                   14
% 11.64/2.00  binary                                  6
% 11.64/2.00  lits                                    160
% 11.64/2.00  lits eq                                 24
% 11.64/2.00  fd_pure                                 0
% 11.64/2.00  fd_pseudo                               0
% 11.64/2.00  fd_cond                                 0
% 11.64/2.00  fd_pseudo_cond                          1
% 11.64/2.00  AC symbols                              0
% 11.64/2.00  
% 11.64/2.00  ------ Input Options Time Limit: Unbounded
% 11.64/2.00  
% 11.64/2.00  
% 11.64/2.00  ------ 
% 11.64/2.00  Current options:
% 11.64/2.00  ------ 
% 11.64/2.00  
% 11.64/2.00  
% 11.64/2.00  
% 11.64/2.00  
% 11.64/2.00  ------ Proving...
% 11.64/2.00  
% 11.64/2.00  
% 11.64/2.00  % SZS status Theorem for theBenchmark.p
% 11.64/2.00  
% 11.64/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.64/2.00  
% 11.64/2.00  fof(f21,conjecture,(
% 11.64/2.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f22,negated_conjecture,(
% 11.64/2.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.64/2.00    inference(negated_conjecture,[],[f21])).
% 11.64/2.00  
% 11.64/2.00  fof(f48,plain,(
% 11.64/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.64/2.00    inference(ennf_transformation,[],[f22])).
% 11.64/2.00  
% 11.64/2.00  fof(f49,plain,(
% 11.64/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.64/2.00    inference(flattening,[],[f48])).
% 11.64/2.00  
% 11.64/2.00  fof(f62,plain,(
% 11.64/2.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 11.64/2.00    introduced(choice_axiom,[])).
% 11.64/2.00  
% 11.64/2.00  fof(f61,plain,(
% 11.64/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 11.64/2.00    introduced(choice_axiom,[])).
% 11.64/2.00  
% 11.64/2.00  fof(f60,plain,(
% 11.64/2.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 11.64/2.00    introduced(choice_axiom,[])).
% 11.64/2.00  
% 11.64/2.00  fof(f59,plain,(
% 11.64/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 11.64/2.00    introduced(choice_axiom,[])).
% 11.64/2.00  
% 11.64/2.00  fof(f58,plain,(
% 11.64/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 11.64/2.00    introduced(choice_axiom,[])).
% 11.64/2.00  
% 11.64/2.00  fof(f57,plain,(
% 11.64/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 11.64/2.00    introduced(choice_axiom,[])).
% 11.64/2.00  
% 11.64/2.00  fof(f63,plain,(
% 11.64/2.00    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 11.64/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f49,f62,f61,f60,f59,f58,f57])).
% 11.64/2.00  
% 11.64/2.00  fof(f99,plain,(
% 11.64/2.00    r1_subset_1(sK2,sK3)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f13,axiom,(
% 11.64/2.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f34,plain,(
% 11.64/2.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.64/2.00    inference(ennf_transformation,[],[f13])).
% 11.64/2.00  
% 11.64/2.00  fof(f35,plain,(
% 11.64/2.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.64/2.00    inference(flattening,[],[f34])).
% 11.64/2.00  
% 11.64/2.00  fof(f53,plain,(
% 11.64/2.00    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.64/2.00    inference(nnf_transformation,[],[f35])).
% 11.64/2.00  
% 11.64/2.00  fof(f78,plain,(
% 11.64/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f53])).
% 11.64/2.00  
% 11.64/2.00  fof(f95,plain,(
% 11.64/2.00    ~v1_xboole_0(sK2)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f97,plain,(
% 11.64/2.00    ~v1_xboole_0(sK3)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f102,plain,(
% 11.64/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f16,axiom,(
% 11.64/2.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f38,plain,(
% 11.64/2.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.64/2.00    inference(ennf_transformation,[],[f16])).
% 11.64/2.00  
% 11.64/2.00  fof(f39,plain,(
% 11.64/2.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.64/2.00    inference(flattening,[],[f38])).
% 11.64/2.00  
% 11.64/2.00  fof(f83,plain,(
% 11.64/2.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f39])).
% 11.64/2.00  
% 11.64/2.00  fof(f94,plain,(
% 11.64/2.00    ~v1_xboole_0(sK1)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f100,plain,(
% 11.64/2.00    v1_funct_1(sK4)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f101,plain,(
% 11.64/2.00    v1_funct_2(sK4,sK2,sK1)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f17,axiom,(
% 11.64/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f40,plain,(
% 11.64/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.64/2.00    inference(ennf_transformation,[],[f17])).
% 11.64/2.00  
% 11.64/2.00  fof(f41,plain,(
% 11.64/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(flattening,[],[f40])).
% 11.64/2.00  
% 11.64/2.00  fof(f54,plain,(
% 11.64/2.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(nnf_transformation,[],[f41])).
% 11.64/2.00  
% 11.64/2.00  fof(f84,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f54])).
% 11.64/2.00  
% 11.64/2.00  fof(f14,axiom,(
% 11.64/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f36,plain,(
% 11.64/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.64/2.00    inference(ennf_transformation,[],[f14])).
% 11.64/2.00  
% 11.64/2.00  fof(f80,plain,(
% 11.64/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.64/2.00    inference(cnf_transformation,[],[f36])).
% 11.64/2.00  
% 11.64/2.00  fof(f15,axiom,(
% 11.64/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f23,plain,(
% 11.64/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.64/2.00    inference(pure_predicate_removal,[],[f15])).
% 11.64/2.00  
% 11.64/2.00  fof(f37,plain,(
% 11.64/2.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.64/2.00    inference(ennf_transformation,[],[f23])).
% 11.64/2.00  
% 11.64/2.00  fof(f81,plain,(
% 11.64/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.64/2.00    inference(cnf_transformation,[],[f37])).
% 11.64/2.00  
% 11.64/2.00  fof(f12,axiom,(
% 11.64/2.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f33,plain,(
% 11.64/2.00    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(ennf_transformation,[],[f12])).
% 11.64/2.00  
% 11.64/2.00  fof(f52,plain,(
% 11.64/2.00    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(nnf_transformation,[],[f33])).
% 11.64/2.00  
% 11.64/2.00  fof(f77,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f52])).
% 11.64/2.00  
% 11.64/2.00  fof(f6,axiom,(
% 11.64/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f27,plain,(
% 11.64/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(ennf_transformation,[],[f6])).
% 11.64/2.00  
% 11.64/2.00  fof(f68,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f27])).
% 11.64/2.00  
% 11.64/2.00  fof(f7,axiom,(
% 11.64/2.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f28,plain,(
% 11.64/2.00    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(ennf_transformation,[],[f7])).
% 11.64/2.00  
% 11.64/2.00  fof(f50,plain,(
% 11.64/2.00    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(nnf_transformation,[],[f28])).
% 11.64/2.00  
% 11.64/2.00  fof(f70,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f50])).
% 11.64/2.00  
% 11.64/2.00  fof(f10,axiom,(
% 11.64/2.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f31,plain,(
% 11.64/2.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 11.64/2.00    inference(ennf_transformation,[],[f10])).
% 11.64/2.00  
% 11.64/2.00  fof(f51,plain,(
% 11.64/2.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.64/2.00    inference(nnf_transformation,[],[f31])).
% 11.64/2.00  
% 11.64/2.00  fof(f74,plain,(
% 11.64/2.00    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f51])).
% 11.64/2.00  
% 11.64/2.00  fof(f2,axiom,(
% 11.64/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f65,plain,(
% 11.64/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.64/2.00    inference(cnf_transformation,[],[f2])).
% 11.64/2.00  
% 11.64/2.00  fof(f11,axiom,(
% 11.64/2.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f32,plain,(
% 11.64/2.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(ennf_transformation,[],[f11])).
% 11.64/2.00  
% 11.64/2.00  fof(f75,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f32])).
% 11.64/2.00  
% 11.64/2.00  fof(f4,axiom,(
% 11.64/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f67,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 11.64/2.00    inference(cnf_transformation,[],[f4])).
% 11.64/2.00  
% 11.64/2.00  fof(f109,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(definition_unfolding,[],[f75,f67])).
% 11.64/2.00  
% 11.64/2.00  fof(f105,plain,(
% 11.64/2.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f18,axiom,(
% 11.64/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f42,plain,(
% 11.64/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.64/2.00    inference(ennf_transformation,[],[f18])).
% 11.64/2.00  
% 11.64/2.00  fof(f43,plain,(
% 11.64/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.64/2.00    inference(flattening,[],[f42])).
% 11.64/2.00  
% 11.64/2.00  fof(f86,plain,(
% 11.64/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f43])).
% 11.64/2.00  
% 11.64/2.00  fof(f103,plain,(
% 11.64/2.00    v1_funct_1(sK5)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f98,plain,(
% 11.64/2.00    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f1,axiom,(
% 11.64/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f25,plain,(
% 11.64/2.00    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.64/2.00    inference(ennf_transformation,[],[f1])).
% 11.64/2.00  
% 11.64/2.00  fof(f64,plain,(
% 11.64/2.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.64/2.00    inference(cnf_transformation,[],[f25])).
% 11.64/2.00  
% 11.64/2.00  fof(f107,plain,(
% 11.64/2.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.64/2.00    inference(definition_unfolding,[],[f64,f67])).
% 11.64/2.00  
% 11.64/2.00  fof(f106,plain,(
% 11.64/2.00    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f96,plain,(
% 11.64/2.00    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f19,axiom,(
% 11.64/2.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f44,plain,(
% 11.64/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.64/2.00    inference(ennf_transformation,[],[f19])).
% 11.64/2.00  
% 11.64/2.00  fof(f45,plain,(
% 11.64/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.64/2.00    inference(flattening,[],[f44])).
% 11.64/2.00  
% 11.64/2.00  fof(f55,plain,(
% 11.64/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.64/2.00    inference(nnf_transformation,[],[f45])).
% 11.64/2.00  
% 11.64/2.00  fof(f56,plain,(
% 11.64/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.64/2.00    inference(flattening,[],[f55])).
% 11.64/2.00  
% 11.64/2.00  fof(f88,plain,(
% 11.64/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f56])).
% 11.64/2.00  
% 11.64/2.00  fof(f113,plain,(
% 11.64/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(equality_resolution,[],[f88])).
% 11.64/2.00  
% 11.64/2.00  fof(f20,axiom,(
% 11.64/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f46,plain,(
% 11.64/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.64/2.00    inference(ennf_transformation,[],[f20])).
% 11.64/2.00  
% 11.64/2.00  fof(f47,plain,(
% 11.64/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.64/2.00    inference(flattening,[],[f46])).
% 11.64/2.00  
% 11.64/2.00  fof(f90,plain,(
% 11.64/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f47])).
% 11.64/2.00  
% 11.64/2.00  fof(f91,plain,(
% 11.64/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f47])).
% 11.64/2.00  
% 11.64/2.00  fof(f92,plain,(
% 11.64/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f47])).
% 11.64/2.00  
% 11.64/2.00  fof(f3,axiom,(
% 11.64/2.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f26,plain,(
% 11.64/2.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.64/2.00    inference(ennf_transformation,[],[f3])).
% 11.64/2.00  
% 11.64/2.00  fof(f66,plain,(
% 11.64/2.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f26])).
% 11.64/2.00  
% 11.64/2.00  fof(f104,plain,(
% 11.64/2.00    v1_funct_2(sK5,sK3,sK1)),
% 11.64/2.00    inference(cnf_transformation,[],[f63])).
% 11.64/2.00  
% 11.64/2.00  fof(f8,axiom,(
% 11.64/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f29,plain,(
% 11.64/2.00    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 11.64/2.00    inference(ennf_transformation,[],[f8])).
% 11.64/2.00  
% 11.64/2.00  fof(f71,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f29])).
% 11.64/2.00  
% 11.64/2.00  fof(f9,axiom,(
% 11.64/2.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 11.64/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.64/2.00  
% 11.64/2.00  fof(f30,plain,(
% 11.64/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.64/2.00    inference(ennf_transformation,[],[f9])).
% 11.64/2.00  
% 11.64/2.00  fof(f72,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f30])).
% 11.64/2.00  
% 11.64/2.00  fof(f108,plain,(
% 11.64/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.64/2.00    inference(definition_unfolding,[],[f72,f67])).
% 11.64/2.00  
% 11.64/2.00  fof(f87,plain,(
% 11.64/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(cnf_transformation,[],[f56])).
% 11.64/2.00  
% 11.64/2.00  fof(f114,plain,(
% 11.64/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.64/2.00    inference(equality_resolution,[],[f87])).
% 11.64/2.00  
% 11.64/2.00  cnf(c_35,negated_conjecture,
% 11.64/2.00      ( r1_subset_1(sK2,sK3) ),
% 11.64/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_571,negated_conjecture,
% 11.64/2.00      ( r1_subset_1(sK2,sK3) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_35]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1340,plain,
% 11.64/2.00      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_14,plain,
% 11.64/2.00      ( ~ r1_subset_1(X0,X1)
% 11.64/2.00      | r1_xboole_0(X0,X1)
% 11.64/2.00      | v1_xboole_0(X0)
% 11.64/2.00      | v1_xboole_0(X1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_589,plain,
% 11.64/2.00      ( ~ r1_subset_1(X0_56,X1_56)
% 11.64/2.00      | r1_xboole_0(X0_56,X1_56)
% 11.64/2.00      | v1_xboole_0(X1_56)
% 11.64/2.00      | v1_xboole_0(X0_56) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_14]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1323,plain,
% 11.64/2.00      ( r1_subset_1(X0_56,X1_56) != iProver_top
% 11.64/2.00      | r1_xboole_0(X0_56,X1_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X1_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_589]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_3939,plain,
% 11.64/2.00      ( r1_xboole_0(sK2,sK3) = iProver_top
% 11.64/2.00      | v1_xboole_0(sK3) = iProver_top
% 11.64/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_1340,c_1323]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_39,negated_conjecture,
% 11.64/2.00      ( ~ v1_xboole_0(sK2) ),
% 11.64/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_44,plain,
% 11.64/2.00      ( v1_xboole_0(sK2) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_37,negated_conjecture,
% 11.64/2.00      ( ~ v1_xboole_0(sK3) ),
% 11.64/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_46,plain,
% 11.64/2.00      ( v1_xboole_0(sK3) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_48,plain,
% 11.64/2.00      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1852,plain,
% 11.64/2.00      ( ~ r1_subset_1(sK2,sK3)
% 11.64/2.00      | r1_xboole_0(sK2,sK3)
% 11.64/2.00      | v1_xboole_0(sK3)
% 11.64/2.00      | v1_xboole_0(sK2) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_589]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1853,plain,
% 11.64/2.00      ( r1_subset_1(sK2,sK3) != iProver_top
% 11.64/2.00      | r1_xboole_0(sK2,sK3) = iProver_top
% 11.64/2.00      | v1_xboole_0(sK3) = iProver_top
% 11.64/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_1852]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_4347,plain,
% 11.64/2.00      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_3939,c_44,c_46,c_48,c_1853]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_32,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.64/2.00      inference(cnf_transformation,[],[f102]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_574,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_32]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1337,plain,
% 11.64/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_17,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | v1_partfun1(X0,X1)
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | v1_xboole_0(X2) ),
% 11.64/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_586,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 11.64/2.00      | v1_partfun1(X0_56,X1_56)
% 11.64/2.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 11.64/2.00      | ~ v1_funct_1(X0_56)
% 11.64/2.00      | v1_xboole_0(X2_56) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_17]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1326,plain,
% 11.64/2.00      ( v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
% 11.64/2.00      | v1_partfun1(X0_56,X1_56) = iProver_top
% 11.64/2.00      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 11.64/2.00      | v1_funct_1(X0_56) != iProver_top
% 11.64/2.00      | v1_xboole_0(X2_56) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_4979,plain,
% 11.64/2.00      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.64/2.00      | v1_partfun1(sK4,sK2) = iProver_top
% 11.64/2.00      | v1_funct_1(sK4) != iProver_top
% 11.64/2.00      | v1_xboole_0(sK1) = iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_1337,c_1326]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_40,negated_conjecture,
% 11.64/2.00      ( ~ v1_xboole_0(sK1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_43,plain,
% 11.64/2.00      ( v1_xboole_0(sK1) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_34,negated_conjecture,
% 11.64/2.00      ( v1_funct_1(sK4) ),
% 11.64/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_49,plain,
% 11.64/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_33,negated_conjecture,
% 11.64/2.00      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_50,plain,
% 11.64/2.00      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_51,plain,
% 11.64/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1958,plain,
% 11.64/2.00      ( ~ v1_funct_2(sK4,X0_56,X1_56)
% 11.64/2.00      | v1_partfun1(sK4,X0_56)
% 11.64/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 11.64/2.00      | ~ v1_funct_1(sK4)
% 11.64/2.00      | v1_xboole_0(X1_56) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_586]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2327,plain,
% 11.64/2.00      ( ~ v1_funct_2(sK4,sK2,sK1)
% 11.64/2.00      | v1_partfun1(sK4,sK2)
% 11.64/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.64/2.00      | ~ v1_funct_1(sK4)
% 11.64/2.00      | v1_xboole_0(sK1) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_1958]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2328,plain,
% 11.64/2.00      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.64/2.00      | v1_partfun1(sK4,sK2) = iProver_top
% 11.64/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.64/2.00      | v1_funct_1(sK4) != iProver_top
% 11.64/2.00      | v1_xboole_0(sK1) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_2327]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5735,plain,
% 11.64/2.00      ( v1_partfun1(sK4,sK2) = iProver_top ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_4979,c_43,c_49,c_50,c_51,c_2328]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_20,plain,
% 11.64/2.00      ( ~ v1_partfun1(X0,X1)
% 11.64/2.00      | ~ v4_relat_1(X0,X1)
% 11.64/2.00      | ~ v1_relat_1(X0)
% 11.64/2.00      | k1_relat_1(X0) = X1 ),
% 11.64/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_584,plain,
% 11.64/2.00      ( ~ v1_partfun1(X0_56,X1_56)
% 11.64/2.00      | ~ v4_relat_1(X0_56,X1_56)
% 11.64/2.00      | ~ v1_relat_1(X0_56)
% 11.64/2.00      | k1_relat_1(X0_56) = X1_56 ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_20]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1328,plain,
% 11.64/2.00      ( k1_relat_1(X0_56) = X1_56
% 11.64/2.00      | v1_partfun1(X0_56,X1_56) != iProver_top
% 11.64/2.00      | v4_relat_1(X0_56,X1_56) != iProver_top
% 11.64/2.00      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_584]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5740,plain,
% 11.64/2.00      ( k1_relat_1(sK4) = sK2
% 11.64/2.00      | v4_relat_1(sK4,sK2) != iProver_top
% 11.64/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_5735,c_1328]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_15,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | v1_relat_1(X0) ),
% 11.64/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_588,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 11.64/2.00      | v1_relat_1(X0_56) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_15]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1805,plain,
% 11.64/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.64/2.00      | v1_relat_1(sK4) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_588]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_16,plain,
% 11.64/2.00      ( v4_relat_1(X0,X1)
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.64/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_587,plain,
% 11.64/2.00      ( v4_relat_1(X0_56,X1_56)
% 11.64/2.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_16]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1831,plain,
% 11.64/2.00      ( v4_relat_1(sK4,sK2)
% 11.64/2.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_587]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2086,plain,
% 11.64/2.00      ( ~ v1_partfun1(sK4,X0_56)
% 11.64/2.00      | ~ v4_relat_1(sK4,X0_56)
% 11.64/2.00      | ~ v1_relat_1(sK4)
% 11.64/2.00      | k1_relat_1(sK4) = X0_56 ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_584]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2119,plain,
% 11.64/2.00      ( ~ v1_partfun1(sK4,sK2)
% 11.64/2.00      | ~ v4_relat_1(sK4,sK2)
% 11.64/2.00      | ~ v1_relat_1(sK4)
% 11.64/2.00      | k1_relat_1(sK4) = sK2 ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_2086]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_6193,plain,
% 11.64/2.00      ( k1_relat_1(sK4) = sK2 ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_5740,c_40,c_34,c_33,c_32,c_1805,c_1831,c_2119,c_2327]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_11,plain,
% 11.64/2.00      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.64/2.00      | ~ v1_relat_1(X0)
% 11.64/2.00      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 11.64/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_592,plain,
% 11.64/2.00      ( ~ r1_xboole_0(k1_relat_1(X0_56),X1_56)
% 11.64/2.00      | ~ v1_relat_1(X0_56)
% 11.64/2.00      | k7_relat_1(X0_56,X1_56) = k1_xboole_0 ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_11]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1320,plain,
% 11.64/2.00      ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
% 11.64/2.00      | r1_xboole_0(k1_relat_1(X0_56),X1_56) != iProver_top
% 11.64/2.00      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_6219,plain,
% 11.64/2.00      ( k7_relat_1(sK4,X0_56) = k1_xboole_0
% 11.64/2.00      | r1_xboole_0(sK2,X0_56) != iProver_top
% 11.64/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_6193,c_1320]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1806,plain,
% 11.64/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.64/2.00      | v1_relat_1(sK4) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_1805]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7475,plain,
% 11.64/2.00      ( r1_xboole_0(sK2,X0_56) != iProver_top
% 11.64/2.00      | k7_relat_1(sK4,X0_56) = k1_xboole_0 ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_6219,c_51,c_1806]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7476,plain,
% 11.64/2.00      ( k7_relat_1(sK4,X0_56) = k1_xboole_0
% 11.64/2.00      | r1_xboole_0(sK2,X0_56) != iProver_top ),
% 11.64/2.00      inference(renaming,[status(thm)],[c_7475]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7483,plain,
% 11.64/2.00      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_4347,c_7476]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1324,plain,
% 11.64/2.00      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 11.64/2.00      | v1_relat_1(X0_56) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2587,plain,
% 11.64/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_1337,c_1324]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_3,plain,
% 11.64/2.00      ( ~ v1_relat_1(X0)
% 11.64/2.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_600,plain,
% 11.64/2.00      ( ~ v1_relat_1(X0_56)
% 11.64/2.00      | k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_3]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1312,plain,
% 11.64/2.00      ( k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56)
% 11.64/2.00      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2746,plain,
% 11.64/2.00      ( k2_relat_1(k7_relat_1(sK4,X0_56)) = k9_relat_1(sK4,X0_56) ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_2587,c_1312]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7648,plain,
% 11.64/2.00      ( k9_relat_1(sK4,sK3) = k2_relat_1(k1_xboole_0) ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_7483,c_2746]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_4,plain,
% 11.64/2.00      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.64/2.00      | ~ v1_relat_1(X0)
% 11.64/2.00      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 11.64/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_599,plain,
% 11.64/2.00      ( ~ r1_xboole_0(k1_relat_1(X0_56),X1_56)
% 11.64/2.00      | ~ v1_relat_1(X0_56)
% 11.64/2.00      | k9_relat_1(X0_56,X1_56) = k1_xboole_0 ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_4]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1313,plain,
% 11.64/2.00      ( k9_relat_1(X0_56,X1_56) = k1_xboole_0
% 11.64/2.00      | r1_xboole_0(k1_relat_1(X0_56),X1_56) != iProver_top
% 11.64/2.00      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_6221,plain,
% 11.64/2.00      ( k9_relat_1(sK4,X0_56) = k1_xboole_0
% 11.64/2.00      | r1_xboole_0(sK2,X0_56) != iProver_top
% 11.64/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_6193,c_1313]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7636,plain,
% 11.64/2.00      ( r1_xboole_0(sK2,X0_56) != iProver_top
% 11.64/2.00      | k9_relat_1(sK4,X0_56) = k1_xboole_0 ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_6221,c_51,c_1806]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7637,plain,
% 11.64/2.00      ( k9_relat_1(sK4,X0_56) = k1_xboole_0
% 11.64/2.00      | r1_xboole_0(sK2,X0_56) != iProver_top ),
% 11.64/2.00      inference(renaming,[status(thm)],[c_7636]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7644,plain,
% 11.64/2.00      ( k9_relat_1(sK4,sK3) = k1_xboole_0 ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_4347,c_7637]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7865,plain,
% 11.64/2.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.64/2.00      inference(light_normalisation,[status(thm)],[c_7648,c_7644]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_8,plain,
% 11.64/2.00      ( ~ v1_relat_1(X0)
% 11.64/2.00      | k1_relat_1(X0) = k1_xboole_0
% 11.64/2.00      | k2_relat_1(X0) != k1_xboole_0 ),
% 11.64/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_595,plain,
% 11.64/2.00      ( ~ v1_relat_1(X0_56)
% 11.64/2.00      | k1_relat_1(X0_56) = k1_xboole_0
% 11.64/2.00      | k2_relat_1(X0_56) != k1_xboole_0 ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_8]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1317,plain,
% 11.64/2.00      ( k1_relat_1(X0_56) = k1_xboole_0
% 11.64/2.00      | k2_relat_1(X0_56) != k1_xboole_0
% 11.64/2.00      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7868,plain,
% 11.64/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 11.64/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_7865,c_1317]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1808,plain,
% 11.64/2.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 11.64/2.00      | v1_relat_1(k1_xboole_0) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_588]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1,plain,
% 11.64/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.64/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_602,plain,
% 11.64/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_56)) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_1]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1809,plain,
% 11.64/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_602]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2274,plain,
% 11.64/2.00      ( ~ v1_relat_1(k1_xboole_0)
% 11.64/2.00      | k1_relat_1(k1_xboole_0) = k1_xboole_0
% 11.64/2.00      | k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_595]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_8385,plain,
% 11.64/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_7868,c_1808,c_1809,c_2274,c_7865]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_10,plain,
% 11.64/2.00      ( ~ v1_relat_1(X0)
% 11.64/2.00      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 11.64/2.00      inference(cnf_transformation,[],[f109]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_593,plain,
% 11.64/2.00      ( ~ v1_relat_1(X0_56)
% 11.64/2.00      | k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56)) = k1_relat_1(k7_relat_1(X0_56,X1_56)) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_10]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1319,plain,
% 11.64/2.00      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56)) = k1_relat_1(k7_relat_1(X0_56,X1_56))
% 11.64/2.00      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_3283,plain,
% 11.64/2.00      ( k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_56)) = k1_relat_1(k7_relat_1(sK4,X0_56)) ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_2587,c_1319]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_6198,plain,
% 11.64/2.00      ( k1_relat_1(k7_relat_1(sK4,X0_56)) = k1_setfam_1(k2_tarski(sK2,X0_56)) ),
% 11.64/2.00      inference(demodulation,[status(thm)],[c_6193,c_3283]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7647,plain,
% 11.64/2.00      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_relat_1(k1_xboole_0) ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_7483,c_6198]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_29,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.64/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_577,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_29]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1334,plain,
% 11.64/2.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_21,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.64/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_583,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 11.64/2.00      | ~ v1_funct_1(X0_56)
% 11.64/2.00      | k2_partfun1(X1_56,X2_56,X0_56,X3_56) = k7_relat_1(X0_56,X3_56) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_21]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1329,plain,
% 11.64/2.00      ( k2_partfun1(X0_56,X1_56,X2_56,X3_56) = k7_relat_1(X2_56,X3_56)
% 11.64/2.00      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 11.64/2.00      | v1_funct_1(X2_56) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_583]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5122,plain,
% 11.64/2.00      ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56)
% 11.64/2.00      | v1_funct_1(sK5) != iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_1334,c_1329]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_31,negated_conjecture,
% 11.64/2.00      ( v1_funct_1(sK5) ),
% 11.64/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1943,plain,
% 11.64/2.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 11.64/2.00      | ~ v1_funct_1(sK5)
% 11.64/2.00      | k2_partfun1(X0_56,X1_56,sK5,X2_56) = k7_relat_1(sK5,X2_56) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_583]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2314,plain,
% 11.64/2.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.64/2.00      | ~ v1_funct_1(sK5)
% 11.64/2.00      | k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_1943]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5316,plain,
% 11.64/2.00      ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_5122,c_31,c_29,c_2314]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_36,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.64/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_570,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_36]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1341,plain,
% 11.64/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_0,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.64/2.00      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 11.64/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_603,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 11.64/2.00      | k9_subset_1(X1_56,X2_56,X0_56) = k1_setfam_1(k2_tarski(X2_56,X0_56)) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_0]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1309,plain,
% 11.64/2.00      ( k9_subset_1(X0_56,X1_56,X2_56) = k1_setfam_1(k2_tarski(X1_56,X2_56))
% 11.64/2.00      | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_603]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2138,plain,
% 11.64/2.00      ( k1_setfam_1(k2_tarski(X0_56,sK3)) = k9_subset_1(sK0,X0_56,sK3) ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_1341,c_1309]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_28,negated_conjecture,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.64/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_578,negated_conjecture,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_28]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2342,plain,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 11.64/2.00      inference(demodulation,[status(thm)],[c_2138,c_578]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5320,plain,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 11.64/2.00      inference(demodulation,[status(thm)],[c_5316,c_2342]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5123,plain,
% 11.64/2.00      ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56)
% 11.64/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_1337,c_1329]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1948,plain,
% 11.64/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 11.64/2.00      | ~ v1_funct_1(sK4)
% 11.64/2.00      | k2_partfun1(X0_56,X1_56,sK4,X2_56) = k7_relat_1(sK4,X2_56) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_583]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2319,plain,
% 11.64/2.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.64/2.00      | ~ v1_funct_1(sK4)
% 11.64/2.00      | k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 11.64/2.00      inference(instantiation,[status(thm)],[c_1948]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5513,plain,
% 11.64/2.00      ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_5123,c_34,c_32,c_2319]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_5517,plain,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 11.64/2.00      inference(demodulation,[status(thm)],[c_5320,c_5513]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_7887,plain,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) != k7_relat_1(sK4,k1_relat_1(k1_xboole_0)) ),
% 11.64/2.00      inference(demodulation,[status(thm)],[c_7647,c_5517]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_8388,plain,
% 11.64/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.64/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.64/2.00      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.64/2.00      inference(demodulation,[status(thm)],[c_8385,c_7887]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_38,negated_conjecture,
% 11.64/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 11.64/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_23,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.64/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | ~ v1_funct_1(X3)
% 11.64/2.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.64/2.00      | v1_xboole_0(X5)
% 11.64/2.00      | v1_xboole_0(X2)
% 11.64/2.00      | v1_xboole_0(X4)
% 11.64/2.00      | v1_xboole_0(X1)
% 11.64/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.64/2.00      inference(cnf_transformation,[],[f113]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_27,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | ~ v1_funct_1(X3)
% 11.64/2.00      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.64/2.00      | v1_xboole_0(X5)
% 11.64/2.00      | v1_xboole_0(X2)
% 11.64/2.00      | v1_xboole_0(X4)
% 11.64/2.00      | v1_xboole_0(X1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_26,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.00      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.64/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | ~ v1_funct_1(X3)
% 11.64/2.00      | v1_xboole_0(X5)
% 11.64/2.00      | v1_xboole_0(X2)
% 11.64/2.00      | v1_xboole_0(X4)
% 11.64/2.00      | v1_xboole_0(X1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_25,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.00      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | ~ v1_funct_1(X3)
% 11.64/2.00      | v1_xboole_0(X5)
% 11.64/2.00      | v1_xboole_0(X2)
% 11.64/2.00      | v1_xboole_0(X4)
% 11.64/2.00      | v1_xboole_0(X1) ),
% 11.64/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_336,plain,
% 11.64/2.00      ( ~ v1_funct_1(X3)
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.00      | ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.00      | v1_xboole_0(X5)
% 11.64/2.00      | v1_xboole_0(X2)
% 11.64/2.00      | v1_xboole_0(X4)
% 11.64/2.00      | v1_xboole_0(X1)
% 11.64/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_23,c_27,c_26,c_25]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_337,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.00      | ~ v1_funct_1(X0)
% 11.64/2.00      | ~ v1_funct_1(X3)
% 11.64/2.00      | v1_xboole_0(X1)
% 11.64/2.00      | v1_xboole_0(X2)
% 11.64/2.00      | v1_xboole_0(X4)
% 11.64/2.00      | v1_xboole_0(X5)
% 11.64/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.64/2.00      inference(renaming,[status(thm)],[c_336]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_564,plain,
% 11.64/2.00      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 11.64/2.00      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 11.64/2.00      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 11.64/2.00      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 11.64/2.00      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 11.64/2.00      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 11.64/2.00      | ~ v1_funct_1(X0_56)
% 11.64/2.00      | ~ v1_funct_1(X3_56)
% 11.64/2.00      | v1_xboole_0(X1_56)
% 11.64/2.00      | v1_xboole_0(X2_56)
% 11.64/2.00      | v1_xboole_0(X4_56)
% 11.64/2.00      | v1_xboole_0(X5_56)
% 11.64/2.00      | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X1_56) = X0_56 ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_337]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1347,plain,
% 11.64/2.00      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X0_56) = X2_56
% 11.64/2.00      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 11.64/2.00      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 11.64/2.00      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.00      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.00      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 11.64/2.00      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 11.64/2.00      | v1_funct_1(X2_56) != iProver_top
% 11.64/2.00      | v1_funct_1(X5_56) != iProver_top
% 11.64/2.00      | v1_xboole_0(X3_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X1_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X4_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_564]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_2,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.64/2.00      | ~ v1_xboole_0(X1)
% 11.64/2.00      | v1_xboole_0(X0) ),
% 11.64/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_601,plain,
% 11.64/2.00      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 11.64/2.00      | ~ v1_xboole_0(X1_56)
% 11.64/2.00      | v1_xboole_0(X0_56) ),
% 11.64/2.00      inference(subtyping,[status(esa)],[c_2]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1311,plain,
% 11.64/2.00      ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
% 11.64/2.00      | v1_xboole_0(X1_56) != iProver_top
% 11.64/2.00      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.00      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_1593,plain,
% 11.64/2.00      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X0_56,X4_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X0_56,X4_56))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X3_56,X0_56,X4_56),X1_56,k1_tmap_1(X3_56,X1_56,X0_56,X4_56,X2_56,X5_56),X4_56) = X5_56
% 11.64/2.00      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 11.64/2.00      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 11.64/2.00      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.00      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.00      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 11.64/2.00      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 11.64/2.00      | v1_funct_1(X5_56) != iProver_top
% 11.64/2.00      | v1_funct_1(X2_56) != iProver_top
% 11.64/2.00      | v1_xboole_0(X0_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X1_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(X4_56) = iProver_top ),
% 11.64/2.00      inference(forward_subsumption_resolution,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_1347,c_1311]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_9623,plain,
% 11.64/2.00      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
% 11.64/2.00      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 11.64/2.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.64/2.00      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.00      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 11.64/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.64/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.00      | v1_funct_1(X1_56) != iProver_top
% 11.64/2.00      | v1_funct_1(sK4) != iProver_top
% 11.64/2.00      | v1_xboole_0(X0_56) = iProver_top
% 11.64/2.00      | v1_xboole_0(sK1) = iProver_top
% 11.64/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.64/2.00      inference(superposition,[status(thm)],[c_5513,c_1593]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_10990,plain,
% 11.64/2.00      ( v1_funct_1(X1_56) != iProver_top
% 11.64/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.00      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 11.64/2.00      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
% 11.64/2.00      | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 11.64/2.00      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.00      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 11.64/2.00      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.00      inference(global_propositional_subsumption,
% 11.64/2.00                [status(thm)],
% 11.64/2.00                [c_9623,c_43,c_44,c_49,c_50,c_51]) ).
% 11.64/2.00  
% 11.64/2.00  cnf(c_10991,plain,
% 11.64/2.00      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 11.64/2.00      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
% 11.64/2.01      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 11.64/2.01      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | v1_funct_1(X1_56) != iProver_top
% 11.64/2.01      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.01      inference(renaming,[status(thm)],[c_10990]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_11004,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 11.64/2.01      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.64/2.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
% 11.64/2.01      | v1_funct_1(sK5) != iProver_top
% 11.64/2.01      | v1_xboole_0(sK3) = iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_5316,c_10991]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_52,plain,
% 11.64/2.01      ( v1_funct_1(sK5) = iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_30,negated_conjecture,
% 11.64/2.01      ( v1_funct_2(sK5,sK3,sK1) ),
% 11.64/2.01      inference(cnf_transformation,[],[f104]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_53,plain,
% 11.64/2.01      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_54,plain,
% 11.64/2.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_12404,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_11004,c_46,c_52,c_53,c_54]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_12414,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_2138,c_12404]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_8389,plain,
% 11.64/2.01      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_8385,c_7647]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_4978,plain,
% 11.64/2.01      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.64/2.01      | v1_partfun1(sK5,sK3) = iProver_top
% 11.64/2.01      | v1_funct_1(sK5) != iProver_top
% 11.64/2.01      | v1_xboole_0(sK1) = iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_1334,c_1326]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1953,plain,
% 11.64/2.01      ( ~ v1_funct_2(sK5,X0_56,X1_56)
% 11.64/2.01      | v1_partfun1(sK5,X0_56)
% 11.64/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 11.64/2.01      | ~ v1_funct_1(sK5)
% 11.64/2.01      | v1_xboole_0(X1_56) ),
% 11.64/2.01      inference(instantiation,[status(thm)],[c_586]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_2324,plain,
% 11.64/2.01      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.64/2.01      | v1_partfun1(sK5,sK3)
% 11.64/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.64/2.01      | ~ v1_funct_1(sK5)
% 11.64/2.01      | v1_xboole_0(sK1) ),
% 11.64/2.01      inference(instantiation,[status(thm)],[c_1953]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_2325,plain,
% 11.64/2.01      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.64/2.01      | v1_partfun1(sK5,sK3) = iProver_top
% 11.64/2.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.64/2.01      | v1_funct_1(sK5) != iProver_top
% 11.64/2.01      | v1_xboole_0(sK1) = iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_2324]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_5727,plain,
% 11.64/2.01      ( v1_partfun1(sK5,sK3) = iProver_top ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_4978,c_43,c_52,c_53,c_54,c_2325]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_5732,plain,
% 11.64/2.01      ( k1_relat_1(sK5) = sK3
% 11.64/2.01      | v4_relat_1(sK5,sK3) != iProver_top
% 11.64/2.01      | v1_relat_1(sK5) != iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_5727,c_1328]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1802,plain,
% 11.64/2.01      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.64/2.01      | v1_relat_1(sK5) ),
% 11.64/2.01      inference(instantiation,[status(thm)],[c_588]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1828,plain,
% 11.64/2.01      ( v4_relat_1(sK5,sK3)
% 11.64/2.01      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.64/2.01      inference(instantiation,[status(thm)],[c_587]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_2050,plain,
% 11.64/2.01      ( ~ v1_partfun1(sK5,X0_56)
% 11.64/2.01      | ~ v4_relat_1(sK5,X0_56)
% 11.64/2.01      | ~ v1_relat_1(sK5)
% 11.64/2.01      | k1_relat_1(sK5) = X0_56 ),
% 11.64/2.01      inference(instantiation,[status(thm)],[c_584]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_2718,plain,
% 11.64/2.01      ( ~ v1_partfun1(sK5,sK3)
% 11.64/2.01      | ~ v4_relat_1(sK5,sK3)
% 11.64/2.01      | ~ v1_relat_1(sK5)
% 11.64/2.01      | k1_relat_1(sK5) = sK3 ),
% 11.64/2.01      inference(instantiation,[status(thm)],[c_2050]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_6124,plain,
% 11.64/2.01      ( k1_relat_1(sK5) = sK3 ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_5732,c_40,c_31,c_30,c_29,c_1802,c_1828,c_2324,c_2718]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_6,plain,
% 11.64/2.01      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 11.64/2.01      | ~ v1_relat_1(X1)
% 11.64/2.01      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 11.64/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_597,plain,
% 11.64/2.01      ( ~ r1_xboole_0(X0_56,k1_relat_1(X1_56))
% 11.64/2.01      | ~ v1_relat_1(X1_56)
% 11.64/2.01      | k7_relat_1(X1_56,X0_56) = k1_xboole_0 ),
% 11.64/2.01      inference(subtyping,[status(esa)],[c_6]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1315,plain,
% 11.64/2.01      ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
% 11.64/2.01      | r1_xboole_0(X1_56,k1_relat_1(X0_56)) != iProver_top
% 11.64/2.01      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_597]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_6151,plain,
% 11.64/2.01      ( k7_relat_1(sK5,X0_56) = k1_xboole_0
% 11.64/2.01      | r1_xboole_0(X0_56,sK3) != iProver_top
% 11.64/2.01      | v1_relat_1(sK5) != iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_6124,c_1315]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1803,plain,
% 11.64/2.01      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.64/2.01      | v1_relat_1(sK5) = iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_1802]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_7124,plain,
% 11.64/2.01      ( r1_xboole_0(X0_56,sK3) != iProver_top
% 11.64/2.01      | k7_relat_1(sK5,X0_56) = k1_xboole_0 ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_6151,c_54,c_1803]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_7125,plain,
% 11.64/2.01      ( k7_relat_1(sK5,X0_56) = k1_xboole_0
% 11.64/2.01      | r1_xboole_0(X0_56,sK3) != iProver_top ),
% 11.64/2.01      inference(renaming,[status(thm)],[c_7124]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_7132,plain,
% 11.64/2.01      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_4347,c_7125]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_2586,plain,
% 11.64/2.01      ( v1_relat_1(sK5) = iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_1334,c_1324]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_3282,plain,
% 11.64/2.01      ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_56)) = k1_relat_1(k7_relat_1(sK5,X0_56)) ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_2586,c_1319]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_6129,plain,
% 11.64/2.01      ( k1_relat_1(k7_relat_1(sK5,X0_56)) = k1_setfam_1(k2_tarski(sK3,X0_56)) ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_6124,c_3282]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_7135,plain,
% 11.64/2.01      ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_7132,c_6129]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_8390,plain,
% 11.64/2.01      ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_xboole_0 ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_8385,c_7135]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_7,plain,
% 11.64/2.01      ( ~ v1_relat_1(X0)
% 11.64/2.01      | k7_relat_1(X0,k1_setfam_1(k2_tarski(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 11.64/2.01      inference(cnf_transformation,[],[f108]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_596,plain,
% 11.64/2.01      ( ~ v1_relat_1(X0_56)
% 11.64/2.01      | k7_relat_1(X0_56,k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56))) = k7_relat_1(X0_56,X1_56) ),
% 11.64/2.01      inference(subtyping,[status(esa)],[c_7]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1316,plain,
% 11.64/2.01      ( k7_relat_1(X0_56,k1_setfam_1(k2_tarski(k1_relat_1(X0_56),X1_56))) = k7_relat_1(X0_56,X1_56)
% 11.64/2.01      | v1_relat_1(X0_56) != iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_3293,plain,
% 11.64/2.01      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_56))) = k7_relat_1(sK5,X0_56) ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_2586,c_1316]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_3576,plain,
% 11.64/2.01      ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0_56))) = k7_relat_1(sK5,X0_56) ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_3293,c_3282]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_6401,plain,
% 11.64/2.01      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,X0_56))) = k7_relat_1(sK5,X0_56) ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_6129,c_3576]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_9177,plain,
% 11.64/2.01      ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_8390,c_6401]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_9191,plain,
% 11.64/2.01      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_9177,c_7132]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_12415,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(light_normalisation,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_12414,c_8389,c_9191]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_12416,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_12415,c_2138]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_12417,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_12416,c_8389]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_12418,plain,
% 11.64/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.64/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.64/2.01      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.64/2.01      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 11.64/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_12417]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_24,plain,
% 11.64/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.01      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.01      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.64/2.01      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.01      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.64/2.01      | ~ v1_funct_1(X0)
% 11.64/2.01      | ~ v1_funct_1(X3)
% 11.64/2.01      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.64/2.01      | v1_xboole_0(X5)
% 11.64/2.01      | v1_xboole_0(X2)
% 11.64/2.01      | v1_xboole_0(X4)
% 11.64/2.01      | v1_xboole_0(X1)
% 11.64/2.01      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.64/2.01      inference(cnf_transformation,[],[f114]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_345,plain,
% 11.64/2.01      ( ~ v1_funct_1(X3)
% 11.64/2.01      | ~ v1_funct_1(X0)
% 11.64/2.01      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.01      | ~ v1_funct_2(X0,X1,X2)
% 11.64/2.01      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.01      | v1_xboole_0(X5)
% 11.64/2.01      | v1_xboole_0(X2)
% 11.64/2.01      | v1_xboole_0(X4)
% 11.64/2.01      | v1_xboole_0(X1)
% 11.64/2.01      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_24,c_27,c_26,c_25]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_346,plain,
% 11.64/2.01      ( ~ v1_funct_2(X0,X1,X2)
% 11.64/2.01      | ~ v1_funct_2(X3,X4,X2)
% 11.64/2.01      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.64/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.64/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.64/2.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.64/2.01      | ~ v1_funct_1(X0)
% 11.64/2.01      | ~ v1_funct_1(X3)
% 11.64/2.01      | v1_xboole_0(X1)
% 11.64/2.01      | v1_xboole_0(X2)
% 11.64/2.01      | v1_xboole_0(X4)
% 11.64/2.01      | v1_xboole_0(X5)
% 11.64/2.01      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.64/2.01      inference(renaming,[status(thm)],[c_345]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_563,plain,
% 11.64/2.01      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 11.64/2.01      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 11.64/2.01      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 11.64/2.01      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 11.64/2.01      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 11.64/2.01      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 11.64/2.01      | ~ v1_funct_1(X0_56)
% 11.64/2.01      | ~ v1_funct_1(X3_56)
% 11.64/2.01      | v1_xboole_0(X1_56)
% 11.64/2.01      | v1_xboole_0(X2_56)
% 11.64/2.01      | v1_xboole_0(X4_56)
% 11.64/2.01      | v1_xboole_0(X5_56)
% 11.64/2.01      | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X4_56) = X3_56 ),
% 11.64/2.01      inference(subtyping,[status(esa)],[c_346]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1348,plain,
% 11.64/2.01      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X4_56) = X5_56
% 11.64/2.01      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 11.64/2.01      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 11.64/2.01      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 11.64/2.01      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 11.64/2.01      | v1_funct_1(X2_56) != iProver_top
% 11.64/2.01      | v1_funct_1(X5_56) != iProver_top
% 11.64/2.01      | v1_xboole_0(X3_56) = iProver_top
% 11.64/2.01      | v1_xboole_0(X1_56) = iProver_top
% 11.64/2.01      | v1_xboole_0(X4_56) = iProver_top
% 11.64/2.01      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.01      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_1621,plain,
% 11.64/2.01      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X0_56,X4_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X0_56,X4_56))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X3_56,X0_56,X4_56),X1_56,k1_tmap_1(X3_56,X1_56,X0_56,X4_56,X2_56,X5_56),X0_56) = X2_56
% 11.64/2.01      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 11.64/2.01      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 11.64/2.01      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 11.64/2.01      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 11.64/2.01      | v1_funct_1(X5_56) != iProver_top
% 11.64/2.01      | v1_funct_1(X2_56) != iProver_top
% 11.64/2.01      | v1_xboole_0(X0_56) = iProver_top
% 11.64/2.01      | v1_xboole_0(X1_56) = iProver_top
% 11.64/2.01      | v1_xboole_0(X4_56) = iProver_top ),
% 11.64/2.01      inference(forward_subsumption_resolution,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_1348,c_1311]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_11247,plain,
% 11.64/2.01      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
% 11.64/2.01      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 11.64/2.01      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.64/2.01      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 11.64/2.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | v1_funct_1(X1_56) != iProver_top
% 11.64/2.01      | v1_funct_1(sK4) != iProver_top
% 11.64/2.01      | v1_xboole_0(X0_56) = iProver_top
% 11.64/2.01      | v1_xboole_0(sK1) = iProver_top
% 11.64/2.01      | v1_xboole_0(sK2) = iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_5513,c_1621]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_14578,plain,
% 11.64/2.01      ( v1_funct_1(X1_56) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 11.64/2.01      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
% 11.64/2.01      | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 11.64/2.01      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 11.64/2.01      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_11247,c_43,c_44,c_49,c_50,c_51]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_14579,plain,
% 11.64/2.01      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 11.64/2.01      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
% 11.64/2.01      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 11.64/2.01      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 11.64/2.01      | v1_funct_1(X1_56) != iProver_top
% 11.64/2.01      | v1_xboole_0(X0_56) = iProver_top ),
% 11.64/2.01      inference(renaming,[status(thm)],[c_14578]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_14592,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 11.64/2.01      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.64/2.01      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
% 11.64/2.01      | v1_funct_1(sK5) != iProver_top
% 11.64/2.01      | v1_xboole_0(sK3) = iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_5316,c_14579]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_17702,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_14592,c_46,c_52,c_53,c_54]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_17712,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_2138,c_17702]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_17713,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(light_normalisation,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_17712,c_8389,c_9191]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_17714,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_17713,c_2138]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_17715,plain,
% 11.64/2.01      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 11.64/2.01      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.64/2.01      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_17714,c_8389]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_17716,plain,
% 11.64/2.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.64/2.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.64/2.01      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.64/2.01      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 11.64/2.01      inference(predicate_to_equality_rev,[status(thm)],[c_17715]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_3294,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_56))) = k7_relat_1(sK4,X0_56) ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_2587,c_1316]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_3749,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0_56))) = k7_relat_1(sK4,X0_56) ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_3294,c_3283]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_6819,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,X0_56))) = k7_relat_1(sK4,X0_56) ),
% 11.64/2.01      inference(demodulation,[status(thm)],[c_6198,c_3749]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_25985,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(sK4,sK3) ),
% 11.64/2.01      inference(superposition,[status(thm)],[c_8389,c_6819]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_26003,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_25985,c_7483]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_36319,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.64/2.01      inference(global_propositional_subsumption,
% 11.64/2.01                [status(thm)],
% 11.64/2.01                [c_8388,c_38,c_36,c_12418,c_17716,c_26003]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(c_36321,plain,
% 11.64/2.01      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 11.64/2.01      inference(light_normalisation,[status(thm)],[c_36319,c_9191]) ).
% 11.64/2.01  
% 11.64/2.01  cnf(contradiction,plain,
% 11.64/2.01      ( $false ),
% 11.64/2.01      inference(minisat,[status(thm)],[c_36321,c_26003]) ).
% 11.64/2.01  
% 11.64/2.01  
% 11.64/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.64/2.01  
% 11.64/2.01  ------                               Statistics
% 11.64/2.01  
% 11.64/2.01  ------ Selected
% 11.64/2.01  
% 11.64/2.01  total_time:                             1.437
% 11.64/2.01  
%------------------------------------------------------------------------------
