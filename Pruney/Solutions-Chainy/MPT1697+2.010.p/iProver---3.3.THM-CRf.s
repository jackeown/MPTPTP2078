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
% DateTime   : Thu Dec  3 12:21:23 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  299 (10416 expanded)
%              Number of clauses        :  197 (2739 expanded)
%              Number of leaves         :   26 (3286 expanded)
%              Depth                    :   31
%              Number of atoms          : 1384 (97893 expanded)
%              Number of equality atoms :  533 (21389 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f46,f60,f59,f58,f57,f56,f55])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f64,f66])).

fof(f105,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f18,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

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
    inference(cnf_transformation,[],[f54])).

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

fof(f19,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(cnf_transformation,[],[f44])).

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
    inference(cnf_transformation,[],[f44])).

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
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f95,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f101,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f104,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(cnf_transformation,[],[f54])).

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

fof(f106,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f61])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1429,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_2325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1452,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2305,plain,
    ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1452])).

cnf(c_3014,plain,
    ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
    inference(superposition,[status(thm)],[c_2325,c_2305])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1435,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_2319,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1435])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1441,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2314,plain,
    ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
    | v1_funct_1(X2_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1441])).

cnf(c_3748,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_2314])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2785,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_3026,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_3885,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3748,c_33,c_31,c_3026])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1432,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2322,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1432])).

cnf(c_3749,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_2314])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2790,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_3031,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_3975,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3749,c_36,c_34,c_3031])).

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
    inference(cnf_transformation,[],[f113])).

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
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f91])).

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
    inference(cnf_transformation,[],[f92])).

cnf(c_241,plain,
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

cnf(c_242,plain,
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
    inference(renaming,[status(thm)],[c_241])).

cnf(c_1422,plain,
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
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_2332,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1422])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
    | ~ v1_xboole_0(X1_57)
    | v1_xboole_0(X0_57) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2306,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
    | v1_xboole_0(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1451])).

cnf(c_2570,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2332,c_2306])).

cnf(c_9344,plain,
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
    inference(superposition,[status(thm)],[c_3975,c_2570])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_45,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_46,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_52,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_53,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13979,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9344,c_45,c_46,c_51,c_52,c_53])).

cnf(c_13980,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_13979])).

cnf(c_13993,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3885,c_13980])).

cnf(c_39,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_48,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16031,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13993,c_48,c_54,c_55,c_56])).

cnf(c_16041,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_16031])).

cnf(c_16,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_571,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_572,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_574,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_41,c_39])).

cnf(c_1421,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_574])).

cnf(c_2333,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1421])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1453,plain,
    ( ~ r1_xboole_0(X0_57,X1_57)
    | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2304,plain,
    ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
    | r1_xboole_0(X0_57,X1_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1453])).

cnf(c_3416,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2333,c_2304])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_22,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_602,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_18,c_22])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_606,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_22,c_18,c_17])).

cnf(c_607,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_606])).

cnf(c_650,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_19,c_607])).

cnf(c_654,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_650,c_22,c_19,c_18,c_17])).

cnf(c_655,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_654])).

cnf(c_1419,plain,
    ( ~ v1_funct_2(X0_57,X1_57,X2_57)
    | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_funct_1(X0_57)
    | v1_xboole_0(X2_57)
    | k1_relat_1(X0_57) = X1_57 ),
    inference(subtyping,[status(esa)],[c_655])).

cnf(c_2335,plain,
    ( k1_relat_1(X0_57) = X1_57
    | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_funct_1(X0_57) != iProver_top
    | v1_xboole_0(X2_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1419])).

cnf(c_4270,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_2335])).

cnf(c_2780,plain,
    ( ~ v1_funct_2(sK4,X0_57,X1_57)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK4) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_3023,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_5215,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4270,c_42,c_36,c_35,c_34,c_3023])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1444,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2311,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_5234,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5215,c_2311])).

cnf(c_1442,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | v1_relat_1(X0_57) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2698,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_2699,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2698])).

cnf(c_5853,plain,
    ( r1_xboole_0(sK2,X0_57) != iProver_top
    | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5234,c_53,c_2699])).

cnf(c_5854,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_5853])).

cnf(c_5861,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2333,c_5854])).

cnf(c_2313,plain,
    ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
    | v1_relat_1(X0_57) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1442])).

cnf(c_3421,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_2313])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_547,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k9_relat_1(k7_relat_1(X2,X3),X4) = k9_relat_1(X2,X4)
    | k1_relat_1(X0) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_548,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),k1_relat_1(X0)) = k9_relat_1(X2,k1_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X3)
    | k9_relat_1(k7_relat_1(X3,X1),k1_relat_1(X0)) = k9_relat_1(X3,k1_relat_1(X0)) ),
    inference(resolution,[status(thm)],[c_18,c_548])).

cnf(c_588,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X3)
    | k9_relat_1(k7_relat_1(X3,X1),k1_relat_1(X0)) = k9_relat_1(X3,k1_relat_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_17])).

cnf(c_1420,plain,
    ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
    | ~ v1_relat_1(X3_57)
    | k9_relat_1(k7_relat_1(X3_57,X1_57),k1_relat_1(X0_57)) = k9_relat_1(X3_57,k1_relat_1(X0_57)) ),
    inference(subtyping,[status(esa)],[c_588])).

cnf(c_2334,plain,
    ( k9_relat_1(k7_relat_1(X0_57,X1_57),k1_relat_1(X2_57)) = k9_relat_1(X0_57,k1_relat_1(X2_57))
    | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1420])).

cnf(c_4143,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_relat_1(sK5)) = k9_relat_1(X0_57,k1_relat_1(sK5))
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_2334])).

cnf(c_4251,plain,
    ( k9_relat_1(k7_relat_1(sK4,sK3),k1_relat_1(sK5)) = k9_relat_1(sK4,k1_relat_1(sK5)) ),
    inference(superposition,[status(thm)],[c_3421,c_4143])).

cnf(c_4269,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_2335])).

cnf(c_2775,plain,
    ( ~ v1_funct_2(sK5,X0_57,X1_57)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_57)
    | k1_relat_1(sK5) = X0_57 ),
    inference(instantiation,[status(thm)],[c_1419])).

cnf(c_3020,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_4881,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4269,c_42,c_33,c_32,c_31,c_3020])).

cnf(c_5451,plain,
    ( k9_relat_1(k7_relat_1(sK4,sK3),sK3) = k9_relat_1(sK4,sK3) ),
    inference(light_normalisation,[status(thm)],[c_4251,c_4881])).

cnf(c_5940,plain,
    ( k9_relat_1(k1_xboole_0,sK3) = k9_relat_1(sK4,sK3) ),
    inference(demodulation,[status(thm)],[c_5861,c_5451])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1449,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,X1_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2308,plain,
    ( k9_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1449])).

cnf(c_5236,plain,
    ( k9_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5215,c_2308])).

cnf(c_6199,plain,
    ( r1_xboole_0(sK2,X0_57) != iProver_top
    | k9_relat_1(sK4,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5236,c_53,c_2699])).

cnf(c_6200,plain,
    ( k9_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(sK2,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_6199])).

cnf(c_6207,plain,
    ( k9_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2333,c_6200])).

cnf(c_6967,plain,
    ( k9_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5940,c_6207])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1448,plain,
    ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2309,plain,
    ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_6969,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6967,c_2309])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1445,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_6970,plain,
    ( r1_xboole_0(k1_xboole_0,sK3) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6969,c_1445])).

cnf(c_2695,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_2696,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2695])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1447,plain,
    ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
    | ~ v1_relat_1(X1_57)
    | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2310,plain,
    ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
    | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1447])).

cnf(c_4901,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4881,c_2310])).

cnf(c_5772,plain,
    ( r1_xboole_0(X0_57,sK3) != iProver_top
    | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4901,c_56,c_2696])).

cnf(c_5773,plain,
    ( k7_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5772])).

cnf(c_5780,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2333,c_5773])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1450,plain,
    ( ~ v1_relat_1(X0_57)
    | v1_relat_1(k7_relat_1(X0_57,X1_57)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2307,plain,
    ( v1_relat_1(X0_57) != iProver_top
    | v1_relat_1(k7_relat_1(X0_57,X1_57)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1450])).

cnf(c_5865,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5780,c_2307])).

cnf(c_7507,plain,
    ( r1_xboole_0(k1_xboole_0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6970,c_56,c_2696,c_5865])).

cnf(c_7513,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7507,c_5773])).

cnf(c_16042,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16041,c_3416,c_7513])).

cnf(c_16043,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16042,c_3014])).

cnf(c_3420,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_2313])).

cnf(c_4144,plain,
    ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_relat_1(sK4)) = k9_relat_1(X0_57,k1_relat_1(sK4))
    | v1_relat_1(X0_57) != iProver_top ),
    inference(superposition,[status(thm)],[c_2322,c_2334])).

cnf(c_4424,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),k1_relat_1(sK4)) = k9_relat_1(sK5,k1_relat_1(sK4)) ),
    inference(superposition,[status(thm)],[c_3420,c_4144])).

cnf(c_5455,plain,
    ( k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4424,c_5215])).

cnf(c_5863,plain,
    ( k9_relat_1(k1_xboole_0,sK2) = k9_relat_1(sK5,sK2) ),
    inference(demodulation,[status(thm)],[c_5780,c_5455])).

cnf(c_14,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1443,plain,
    ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
    | ~ v1_relat_1(X0_57)
    | k7_relat_1(X0_57,X1_57) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2312,plain,
    ( k7_relat_1(X0_57,X1_57) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
    | v1_relat_1(X0_57) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_5864,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5780,c_2312])).

cnf(c_5880,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5864,c_4881])).

cnf(c_5955,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5880,c_56,c_2696])).

cnf(c_4902,plain,
    ( k9_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4881,c_2308])).

cnf(c_5782,plain,
    ( r1_xboole_0(sK3,X0_57) != iProver_top
    | k9_relat_1(sK5,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4902,c_56,c_2696])).

cnf(c_5783,plain,
    ( k9_relat_1(sK5,X0_57) = k1_xboole_0
    | r1_xboole_0(sK3,X0_57) != iProver_top ),
    inference(renaming,[status(thm)],[c_5782])).

cnf(c_5961,plain,
    ( k9_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5955,c_5783])).

cnf(c_6861,plain,
    ( k9_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5863,c_5961])).

cnf(c_6863,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6861,c_2309])).

cnf(c_6864,plain,
    ( r1_xboole_0(k1_xboole_0,sK2) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6863,c_1445])).

cnf(c_7488,plain,
    ( r1_xboole_0(k1_xboole_0,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6864,c_56,c_2696,c_5865])).

cnf(c_5235,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5215,c_2310])).

cnf(c_6081,plain,
    ( r1_xboole_0(X0_57,sK2) != iProver_top
    | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5235,c_53,c_2699])).

cnf(c_6082,plain,
    ( k7_relat_1(sK4,X0_57) = k1_xboole_0
    | r1_xboole_0(X0_57,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6081])).

cnf(c_7496,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7488,c_6082])).

cnf(c_16044,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16043,c_3416,c_7496])).

cnf(c_16045,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_16044])).

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
    inference(cnf_transformation,[],[f114])).

cnf(c_234,plain,
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

cnf(c_235,plain,
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
    inference(renaming,[status(thm)],[c_234])).

cnf(c_1423,plain,
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
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_2331,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1423])).

cnf(c_2542,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2331,c_2306])).

cnf(c_8283,plain,
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
    inference(superposition,[status(thm)],[c_3975,c_2542])).

cnf(c_9195,plain,
    ( v1_funct_1(X1_57) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8283,c_45,c_46,c_51,c_52,c_53])).

cnf(c_9196,plain,
    ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
    | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
    | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
    | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
    | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
    | v1_funct_1(X1_57) != iProver_top
    | v1_xboole_0(X0_57) = iProver_top ),
    inference(renaming,[status(thm)],[c_9195])).

cnf(c_9209,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3885,c_9196])).

cnf(c_10043,plain,
    ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9209,c_48,c_54,c_55,c_56])).

cnf(c_10053,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3014,c_10043])).

cnf(c_10054,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10053,c_3416,c_7513])).

cnf(c_10055,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10054,c_3014])).

cnf(c_10056,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10055,c_3416,c_7496])).

cnf(c_10057,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10056])).

cnf(c_30,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1436,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_3192,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_3014,c_1436])).

cnf(c_3569,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3416,c_3192])).

cnf(c_3889,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3885,c_3569])).

cnf(c_3979,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3889,c_3975])).

cnf(c_7636,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7496,c_3979])).

cnf(c_49,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16045,c_10057,c_7636,c_7513,c_49,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:16:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.22/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/1.49  
% 7.22/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.22/1.49  
% 7.22/1.49  ------  iProver source info
% 7.22/1.49  
% 7.22/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.22/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.22/1.49  git: non_committed_changes: false
% 7.22/1.49  git: last_make_outside_of_git: false
% 7.22/1.49  
% 7.22/1.49  ------ 
% 7.22/1.49  
% 7.22/1.49  ------ Input Options
% 7.22/1.49  
% 7.22/1.49  --out_options                           all
% 7.22/1.49  --tptp_safe_out                         true
% 7.22/1.49  --problem_path                          ""
% 7.22/1.49  --include_path                          ""
% 7.22/1.49  --clausifier                            res/vclausify_rel
% 7.22/1.49  --clausifier_options                    --mode clausify
% 7.22/1.49  --stdin                                 false
% 7.22/1.49  --stats_out                             all
% 7.22/1.49  
% 7.22/1.49  ------ General Options
% 7.22/1.49  
% 7.22/1.49  --fof                                   false
% 7.22/1.49  --time_out_real                         305.
% 7.22/1.49  --time_out_virtual                      -1.
% 7.22/1.49  --symbol_type_check                     false
% 7.22/1.49  --clausify_out                          false
% 7.22/1.49  --sig_cnt_out                           false
% 7.22/1.49  --trig_cnt_out                          false
% 7.22/1.49  --trig_cnt_out_tolerance                1.
% 7.22/1.49  --trig_cnt_out_sk_spl                   false
% 7.22/1.49  --abstr_cl_out                          false
% 7.22/1.49  
% 7.22/1.49  ------ Global Options
% 7.22/1.49  
% 7.22/1.49  --schedule                              default
% 7.22/1.49  --add_important_lit                     false
% 7.22/1.49  --prop_solver_per_cl                    1000
% 7.22/1.49  --min_unsat_core                        false
% 7.22/1.49  --soft_assumptions                      false
% 7.22/1.49  --soft_lemma_size                       3
% 7.22/1.49  --prop_impl_unit_size                   0
% 7.22/1.49  --prop_impl_unit                        []
% 7.22/1.49  --share_sel_clauses                     true
% 7.22/1.49  --reset_solvers                         false
% 7.22/1.49  --bc_imp_inh                            [conj_cone]
% 7.22/1.49  --conj_cone_tolerance                   3.
% 7.22/1.49  --extra_neg_conj                        none
% 7.22/1.49  --large_theory_mode                     true
% 7.22/1.49  --prolific_symb_bound                   200
% 7.22/1.49  --lt_threshold                          2000
% 7.22/1.49  --clause_weak_htbl                      true
% 7.22/1.49  --gc_record_bc_elim                     false
% 7.22/1.49  
% 7.22/1.49  ------ Preprocessing Options
% 7.22/1.49  
% 7.22/1.49  --preprocessing_flag                    true
% 7.22/1.49  --time_out_prep_mult                    0.1
% 7.22/1.49  --splitting_mode                        input
% 7.22/1.49  --splitting_grd                         true
% 7.22/1.49  --splitting_cvd                         false
% 7.22/1.49  --splitting_cvd_svl                     false
% 7.22/1.49  --splitting_nvd                         32
% 7.22/1.49  --sub_typing                            true
% 7.22/1.49  --prep_gs_sim                           true
% 7.22/1.49  --prep_unflatten                        true
% 7.22/1.49  --prep_res_sim                          true
% 7.22/1.49  --prep_upred                            true
% 7.22/1.49  --prep_sem_filter                       exhaustive
% 7.22/1.49  --prep_sem_filter_out                   false
% 7.22/1.49  --pred_elim                             true
% 7.22/1.49  --res_sim_input                         true
% 7.22/1.49  --eq_ax_congr_red                       true
% 7.22/1.49  --pure_diseq_elim                       true
% 7.22/1.49  --brand_transform                       false
% 7.22/1.49  --non_eq_to_eq                          false
% 7.22/1.49  --prep_def_merge                        true
% 7.22/1.49  --prep_def_merge_prop_impl              false
% 7.22/1.49  --prep_def_merge_mbd                    true
% 7.22/1.49  --prep_def_merge_tr_red                 false
% 7.22/1.49  --prep_def_merge_tr_cl                  false
% 7.22/1.49  --smt_preprocessing                     true
% 7.22/1.49  --smt_ac_axioms                         fast
% 7.22/1.49  --preprocessed_out                      false
% 7.22/1.49  --preprocessed_stats                    false
% 7.22/1.49  
% 7.22/1.49  ------ Abstraction refinement Options
% 7.22/1.49  
% 7.22/1.49  --abstr_ref                             []
% 7.22/1.49  --abstr_ref_prep                        false
% 7.22/1.49  --abstr_ref_until_sat                   false
% 7.22/1.49  --abstr_ref_sig_restrict                funpre
% 7.22/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.22/1.49  --abstr_ref_under                       []
% 7.22/1.49  
% 7.22/1.49  ------ SAT Options
% 7.22/1.49  
% 7.22/1.49  --sat_mode                              false
% 7.22/1.49  --sat_fm_restart_options                ""
% 7.22/1.49  --sat_gr_def                            false
% 7.22/1.49  --sat_epr_types                         true
% 7.22/1.49  --sat_non_cyclic_types                  false
% 7.22/1.49  --sat_finite_models                     false
% 7.22/1.49  --sat_fm_lemmas                         false
% 7.22/1.49  --sat_fm_prep                           false
% 7.22/1.49  --sat_fm_uc_incr                        true
% 7.22/1.49  --sat_out_model                         small
% 7.22/1.49  --sat_out_clauses                       false
% 7.22/1.49  
% 7.22/1.49  ------ QBF Options
% 7.22/1.49  
% 7.22/1.49  --qbf_mode                              false
% 7.22/1.49  --qbf_elim_univ                         false
% 7.22/1.49  --qbf_dom_inst                          none
% 7.22/1.49  --qbf_dom_pre_inst                      false
% 7.22/1.49  --qbf_sk_in                             false
% 7.22/1.49  --qbf_pred_elim                         true
% 7.22/1.49  --qbf_split                             512
% 7.22/1.49  
% 7.22/1.49  ------ BMC1 Options
% 7.22/1.49  
% 7.22/1.49  --bmc1_incremental                      false
% 7.22/1.49  --bmc1_axioms                           reachable_all
% 7.22/1.49  --bmc1_min_bound                        0
% 7.22/1.49  --bmc1_max_bound                        -1
% 7.22/1.49  --bmc1_max_bound_default                -1
% 7.22/1.49  --bmc1_symbol_reachability              true
% 7.22/1.49  --bmc1_property_lemmas                  false
% 7.22/1.49  --bmc1_k_induction                      false
% 7.22/1.49  --bmc1_non_equiv_states                 false
% 7.22/1.49  --bmc1_deadlock                         false
% 7.22/1.49  --bmc1_ucm                              false
% 7.22/1.49  --bmc1_add_unsat_core                   none
% 7.22/1.49  --bmc1_unsat_core_children              false
% 7.22/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.22/1.49  --bmc1_out_stat                         full
% 7.22/1.49  --bmc1_ground_init                      false
% 7.22/1.49  --bmc1_pre_inst_next_state              false
% 7.22/1.49  --bmc1_pre_inst_state                   false
% 7.22/1.49  --bmc1_pre_inst_reach_state             false
% 7.22/1.49  --bmc1_out_unsat_core                   false
% 7.22/1.49  --bmc1_aig_witness_out                  false
% 7.22/1.49  --bmc1_verbose                          false
% 7.22/1.49  --bmc1_dump_clauses_tptp                false
% 7.22/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.22/1.49  --bmc1_dump_file                        -
% 7.22/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.22/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.22/1.49  --bmc1_ucm_extend_mode                  1
% 7.22/1.49  --bmc1_ucm_init_mode                    2
% 7.22/1.49  --bmc1_ucm_cone_mode                    none
% 7.22/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.22/1.49  --bmc1_ucm_relax_model                  4
% 7.22/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.22/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.22/1.49  --bmc1_ucm_layered_model                none
% 7.22/1.49  --bmc1_ucm_max_lemma_size               10
% 7.22/1.49  
% 7.22/1.49  ------ AIG Options
% 7.22/1.49  
% 7.22/1.49  --aig_mode                              false
% 7.22/1.49  
% 7.22/1.49  ------ Instantiation Options
% 7.22/1.49  
% 7.22/1.49  --instantiation_flag                    true
% 7.22/1.49  --inst_sos_flag                         false
% 7.22/1.49  --inst_sos_phase                        true
% 7.22/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.22/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.22/1.49  --inst_lit_sel_side                     num_symb
% 7.22/1.49  --inst_solver_per_active                1400
% 7.22/1.49  --inst_solver_calls_frac                1.
% 7.22/1.49  --inst_passive_queue_type               priority_queues
% 7.22/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.22/1.49  --inst_passive_queues_freq              [25;2]
% 7.22/1.49  --inst_dismatching                      true
% 7.22/1.49  --inst_eager_unprocessed_to_passive     true
% 7.22/1.49  --inst_prop_sim_given                   true
% 7.22/1.49  --inst_prop_sim_new                     false
% 7.22/1.49  --inst_subs_new                         false
% 7.22/1.49  --inst_eq_res_simp                      false
% 7.22/1.49  --inst_subs_given                       false
% 7.22/1.49  --inst_orphan_elimination               true
% 7.22/1.49  --inst_learning_loop_flag               true
% 7.22/1.49  --inst_learning_start                   3000
% 7.22/1.49  --inst_learning_factor                  2
% 7.22/1.49  --inst_start_prop_sim_after_learn       3
% 7.22/1.49  --inst_sel_renew                        solver
% 7.22/1.49  --inst_lit_activity_flag                true
% 7.22/1.49  --inst_restr_to_given                   false
% 7.22/1.49  --inst_activity_threshold               500
% 7.22/1.49  --inst_out_proof                        true
% 7.22/1.49  
% 7.22/1.49  ------ Resolution Options
% 7.22/1.49  
% 7.22/1.49  --resolution_flag                       true
% 7.22/1.49  --res_lit_sel                           adaptive
% 7.22/1.49  --res_lit_sel_side                      none
% 7.22/1.49  --res_ordering                          kbo
% 7.22/1.49  --res_to_prop_solver                    active
% 7.22/1.49  --res_prop_simpl_new                    false
% 7.22/1.49  --res_prop_simpl_given                  true
% 7.22/1.49  --res_passive_queue_type                priority_queues
% 7.22/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.22/1.49  --res_passive_queues_freq               [15;5]
% 7.22/1.49  --res_forward_subs                      full
% 7.22/1.49  --res_backward_subs                     full
% 7.22/1.49  --res_forward_subs_resolution           true
% 7.22/1.49  --res_backward_subs_resolution          true
% 7.22/1.49  --res_orphan_elimination                true
% 7.22/1.49  --res_time_limit                        2.
% 7.22/1.49  --res_out_proof                         true
% 7.22/1.49  
% 7.22/1.49  ------ Superposition Options
% 7.22/1.49  
% 7.22/1.49  --superposition_flag                    true
% 7.22/1.49  --sup_passive_queue_type                priority_queues
% 7.22/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.22/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.22/1.49  --demod_completeness_check              fast
% 7.22/1.49  --demod_use_ground                      true
% 7.22/1.49  --sup_to_prop_solver                    passive
% 7.22/1.49  --sup_prop_simpl_new                    true
% 7.22/1.49  --sup_prop_simpl_given                  true
% 7.22/1.49  --sup_fun_splitting                     false
% 7.22/1.49  --sup_smt_interval                      50000
% 7.22/1.49  
% 7.22/1.49  ------ Superposition Simplification Setup
% 7.22/1.49  
% 7.22/1.49  --sup_indices_passive                   []
% 7.22/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.22/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.22/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.22/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.22/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.22/1.49  --sup_full_bw                           [BwDemod]
% 7.22/1.49  --sup_immed_triv                        [TrivRules]
% 7.22/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.22/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.22/1.49  --sup_immed_bw_main                     []
% 7.22/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.22/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.22/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.22/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.22/1.49  
% 7.22/1.49  ------ Combination Options
% 7.22/1.49  
% 7.22/1.49  --comb_res_mult                         3
% 7.22/1.49  --comb_sup_mult                         2
% 7.22/1.49  --comb_inst_mult                        10
% 7.22/1.49  
% 7.22/1.49  ------ Debug Options
% 7.22/1.49  
% 7.22/1.49  --dbg_backtrace                         false
% 7.22/1.49  --dbg_dump_prop_clauses                 false
% 7.22/1.49  --dbg_dump_prop_clauses_file            -
% 7.22/1.49  --dbg_out_stat                          false
% 7.22/1.49  ------ Parsing...
% 7.22/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.22/1.49  
% 7.22/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.22/1.49  
% 7.22/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.22/1.49  
% 7.22/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.22/1.49  ------ Proving...
% 7.22/1.49  ------ Problem Properties 
% 7.22/1.49  
% 7.22/1.49  
% 7.22/1.49  clauses                                 36
% 7.22/1.49  conjectures                             13
% 7.22/1.49  EPR                                     9
% 7.22/1.49  Horn                                    29
% 7.22/1.49  unary                                   15
% 7.22/1.49  binary                                  5
% 7.22/1.49  lits                                    141
% 7.22/1.49  lits eq                                 22
% 7.22/1.49  fd_pure                                 0
% 7.22/1.49  fd_pseudo                               0
% 7.22/1.49  fd_cond                                 0
% 7.22/1.49  fd_pseudo_cond                          1
% 7.22/1.49  AC symbols                              0
% 7.22/1.49  
% 7.22/1.49  ------ Schedule dynamic 5 is on 
% 7.22/1.49  
% 7.22/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.22/1.49  
% 7.22/1.49  
% 7.22/1.49  ------ 
% 7.22/1.49  Current options:
% 7.22/1.49  ------ 
% 7.22/1.49  
% 7.22/1.49  ------ Input Options
% 7.22/1.49  
% 7.22/1.49  --out_options                           all
% 7.22/1.49  --tptp_safe_out                         true
% 7.22/1.49  --problem_path                          ""
% 7.22/1.49  --include_path                          ""
% 7.22/1.49  --clausifier                            res/vclausify_rel
% 7.22/1.49  --clausifier_options                    --mode clausify
% 7.22/1.49  --stdin                                 false
% 7.22/1.49  --stats_out                             all
% 7.22/1.49  
% 7.22/1.49  ------ General Options
% 7.22/1.49  
% 7.22/1.49  --fof                                   false
% 7.22/1.49  --time_out_real                         305.
% 7.22/1.49  --time_out_virtual                      -1.
% 7.22/1.49  --symbol_type_check                     false
% 7.22/1.49  --clausify_out                          false
% 7.22/1.49  --sig_cnt_out                           false
% 7.22/1.49  --trig_cnt_out                          false
% 7.22/1.49  --trig_cnt_out_tolerance                1.
% 7.22/1.49  --trig_cnt_out_sk_spl                   false
% 7.22/1.49  --abstr_cl_out                          false
% 7.22/1.49  
% 7.22/1.49  ------ Global Options
% 7.22/1.49  
% 7.22/1.49  --schedule                              default
% 7.22/1.49  --add_important_lit                     false
% 7.22/1.49  --prop_solver_per_cl                    1000
% 7.22/1.49  --min_unsat_core                        false
% 7.22/1.49  --soft_assumptions                      false
% 7.22/1.49  --soft_lemma_size                       3
% 7.22/1.49  --prop_impl_unit_size                   0
% 7.22/1.49  --prop_impl_unit                        []
% 7.22/1.49  --share_sel_clauses                     true
% 7.22/1.49  --reset_solvers                         false
% 7.22/1.49  --bc_imp_inh                            [conj_cone]
% 7.22/1.49  --conj_cone_tolerance                   3.
% 7.22/1.49  --extra_neg_conj                        none
% 7.22/1.49  --large_theory_mode                     true
% 7.22/1.49  --prolific_symb_bound                   200
% 7.22/1.49  --lt_threshold                          2000
% 7.22/1.49  --clause_weak_htbl                      true
% 7.22/1.49  --gc_record_bc_elim                     false
% 7.22/1.49  
% 7.22/1.49  ------ Preprocessing Options
% 7.22/1.49  
% 7.22/1.49  --preprocessing_flag                    true
% 7.22/1.49  --time_out_prep_mult                    0.1
% 7.22/1.49  --splitting_mode                        input
% 7.22/1.49  --splitting_grd                         true
% 7.22/1.49  --splitting_cvd                         false
% 7.22/1.49  --splitting_cvd_svl                     false
% 7.22/1.49  --splitting_nvd                         32
% 7.22/1.49  --sub_typing                            true
% 7.22/1.49  --prep_gs_sim                           true
% 7.22/1.49  --prep_unflatten                        true
% 7.22/1.49  --prep_res_sim                          true
% 7.22/1.49  --prep_upred                            true
% 7.22/1.49  --prep_sem_filter                       exhaustive
% 7.22/1.49  --prep_sem_filter_out                   false
% 7.22/1.49  --pred_elim                             true
% 7.22/1.49  --res_sim_input                         true
% 7.22/1.49  --eq_ax_congr_red                       true
% 7.22/1.49  --pure_diseq_elim                       true
% 7.22/1.49  --brand_transform                       false
% 7.22/1.49  --non_eq_to_eq                          false
% 7.22/1.49  --prep_def_merge                        true
% 7.22/1.49  --prep_def_merge_prop_impl              false
% 7.22/1.49  --prep_def_merge_mbd                    true
% 7.22/1.49  --prep_def_merge_tr_red                 false
% 7.22/1.49  --prep_def_merge_tr_cl                  false
% 7.22/1.49  --smt_preprocessing                     true
% 7.22/1.49  --smt_ac_axioms                         fast
% 7.22/1.49  --preprocessed_out                      false
% 7.22/1.49  --preprocessed_stats                    false
% 7.22/1.49  
% 7.22/1.49  ------ Abstraction refinement Options
% 7.22/1.49  
% 7.22/1.49  --abstr_ref                             []
% 7.22/1.49  --abstr_ref_prep                        false
% 7.22/1.49  --abstr_ref_until_sat                   false
% 7.22/1.49  --abstr_ref_sig_restrict                funpre
% 7.22/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.22/1.49  --abstr_ref_under                       []
% 7.22/1.49  
% 7.22/1.49  ------ SAT Options
% 7.22/1.49  
% 7.22/1.49  --sat_mode                              false
% 7.22/1.49  --sat_fm_restart_options                ""
% 7.22/1.49  --sat_gr_def                            false
% 7.22/1.49  --sat_epr_types                         true
% 7.22/1.49  --sat_non_cyclic_types                  false
% 7.22/1.49  --sat_finite_models                     false
% 7.22/1.49  --sat_fm_lemmas                         false
% 7.22/1.49  --sat_fm_prep                           false
% 7.22/1.49  --sat_fm_uc_incr                        true
% 7.22/1.49  --sat_out_model                         small
% 7.22/1.49  --sat_out_clauses                       false
% 7.22/1.49  
% 7.22/1.49  ------ QBF Options
% 7.22/1.49  
% 7.22/1.49  --qbf_mode                              false
% 7.22/1.49  --qbf_elim_univ                         false
% 7.22/1.49  --qbf_dom_inst                          none
% 7.22/1.49  --qbf_dom_pre_inst                      false
% 7.22/1.49  --qbf_sk_in                             false
% 7.22/1.49  --qbf_pred_elim                         true
% 7.22/1.49  --qbf_split                             512
% 7.22/1.49  
% 7.22/1.49  ------ BMC1 Options
% 7.22/1.49  
% 7.22/1.49  --bmc1_incremental                      false
% 7.22/1.49  --bmc1_axioms                           reachable_all
% 7.22/1.49  --bmc1_min_bound                        0
% 7.22/1.49  --bmc1_max_bound                        -1
% 7.22/1.49  --bmc1_max_bound_default                -1
% 7.22/1.49  --bmc1_symbol_reachability              true
% 7.22/1.49  --bmc1_property_lemmas                  false
% 7.22/1.49  --bmc1_k_induction                      false
% 7.22/1.49  --bmc1_non_equiv_states                 false
% 7.22/1.49  --bmc1_deadlock                         false
% 7.22/1.49  --bmc1_ucm                              false
% 7.22/1.49  --bmc1_add_unsat_core                   none
% 7.22/1.49  --bmc1_unsat_core_children              false
% 7.22/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.22/1.49  --bmc1_out_stat                         full
% 7.22/1.49  --bmc1_ground_init                      false
% 7.22/1.49  --bmc1_pre_inst_next_state              false
% 7.22/1.49  --bmc1_pre_inst_state                   false
% 7.22/1.49  --bmc1_pre_inst_reach_state             false
% 7.22/1.49  --bmc1_out_unsat_core                   false
% 7.22/1.49  --bmc1_aig_witness_out                  false
% 7.22/1.49  --bmc1_verbose                          false
% 7.22/1.49  --bmc1_dump_clauses_tptp                false
% 7.22/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.22/1.49  --bmc1_dump_file                        -
% 7.22/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.22/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.22/1.49  --bmc1_ucm_extend_mode                  1
% 7.22/1.49  --bmc1_ucm_init_mode                    2
% 7.22/1.49  --bmc1_ucm_cone_mode                    none
% 7.22/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.22/1.49  --bmc1_ucm_relax_model                  4
% 7.22/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.22/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.22/1.49  --bmc1_ucm_layered_model                none
% 7.22/1.49  --bmc1_ucm_max_lemma_size               10
% 7.22/1.49  
% 7.22/1.49  ------ AIG Options
% 7.22/1.49  
% 7.22/1.49  --aig_mode                              false
% 7.22/1.49  
% 7.22/1.49  ------ Instantiation Options
% 7.22/1.49  
% 7.22/1.49  --instantiation_flag                    true
% 7.22/1.49  --inst_sos_flag                         false
% 7.22/1.49  --inst_sos_phase                        true
% 7.22/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.22/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.22/1.49  --inst_lit_sel_side                     none
% 7.22/1.49  --inst_solver_per_active                1400
% 7.22/1.49  --inst_solver_calls_frac                1.
% 7.22/1.49  --inst_passive_queue_type               priority_queues
% 7.22/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.22/1.49  --inst_passive_queues_freq              [25;2]
% 7.22/1.49  --inst_dismatching                      true
% 7.22/1.49  --inst_eager_unprocessed_to_passive     true
% 7.22/1.49  --inst_prop_sim_given                   true
% 7.22/1.49  --inst_prop_sim_new                     false
% 7.22/1.49  --inst_subs_new                         false
% 7.22/1.49  --inst_eq_res_simp                      false
% 7.22/1.49  --inst_subs_given                       false
% 7.22/1.49  --inst_orphan_elimination               true
% 7.22/1.49  --inst_learning_loop_flag               true
% 7.22/1.49  --inst_learning_start                   3000
% 7.22/1.49  --inst_learning_factor                  2
% 7.22/1.49  --inst_start_prop_sim_after_learn       3
% 7.22/1.49  --inst_sel_renew                        solver
% 7.22/1.49  --inst_lit_activity_flag                true
% 7.22/1.49  --inst_restr_to_given                   false
% 7.22/1.49  --inst_activity_threshold               500
% 7.22/1.49  --inst_out_proof                        true
% 7.22/1.49  
% 7.22/1.49  ------ Resolution Options
% 7.22/1.49  
% 7.22/1.49  --resolution_flag                       false
% 7.22/1.49  --res_lit_sel                           adaptive
% 7.22/1.49  --res_lit_sel_side                      none
% 7.22/1.49  --res_ordering                          kbo
% 7.22/1.49  --res_to_prop_solver                    active
% 7.22/1.49  --res_prop_simpl_new                    false
% 7.22/1.49  --res_prop_simpl_given                  true
% 7.22/1.49  --res_passive_queue_type                priority_queues
% 7.22/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.22/1.49  --res_passive_queues_freq               [15;5]
% 7.22/1.49  --res_forward_subs                      full
% 7.22/1.49  --res_backward_subs                     full
% 7.22/1.49  --res_forward_subs_resolution           true
% 7.22/1.49  --res_backward_subs_resolution          true
% 7.22/1.49  --res_orphan_elimination                true
% 7.22/1.49  --res_time_limit                        2.
% 7.22/1.49  --res_out_proof                         true
% 7.22/1.49  
% 7.22/1.49  ------ Superposition Options
% 7.22/1.49  
% 7.22/1.49  --superposition_flag                    true
% 7.22/1.49  --sup_passive_queue_type                priority_queues
% 7.22/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.22/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.22/1.49  --demod_completeness_check              fast
% 7.22/1.49  --demod_use_ground                      true
% 7.22/1.49  --sup_to_prop_solver                    passive
% 7.22/1.49  --sup_prop_simpl_new                    true
% 7.22/1.49  --sup_prop_simpl_given                  true
% 7.22/1.49  --sup_fun_splitting                     false
% 7.22/1.49  --sup_smt_interval                      50000
% 7.22/1.49  
% 7.22/1.49  ------ Superposition Simplification Setup
% 7.22/1.49  
% 7.22/1.49  --sup_indices_passive                   []
% 7.22/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.22/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.22/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.22/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.22/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.22/1.49  --sup_full_bw                           [BwDemod]
% 7.22/1.49  --sup_immed_triv                        [TrivRules]
% 7.22/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.22/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.22/1.49  --sup_immed_bw_main                     []
% 7.22/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.22/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.22/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.22/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.22/1.49  
% 7.22/1.49  ------ Combination Options
% 7.22/1.49  
% 7.22/1.49  --comb_res_mult                         3
% 7.22/1.49  --comb_sup_mult                         2
% 7.22/1.49  --comb_inst_mult                        10
% 7.22/1.49  
% 7.22/1.49  ------ Debug Options
% 7.22/1.49  
% 7.22/1.49  --dbg_backtrace                         false
% 7.22/1.49  --dbg_dump_prop_clauses                 false
% 7.22/1.49  --dbg_dump_prop_clauses_file            -
% 7.22/1.49  --dbg_out_stat                          false
% 7.22/1.49  
% 7.22/1.49  
% 7.22/1.49  
% 7.22/1.49  
% 7.22/1.49  ------ Proving...
% 7.22/1.49  
% 7.22/1.49  
% 7.22/1.49  % SZS status Theorem for theBenchmark.p
% 7.22/1.49  
% 7.22/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.22/1.49  
% 7.22/1.49  fof(f20,conjecture,(
% 7.22/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f21,negated_conjecture,(
% 7.22/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.22/1.50    inference(negated_conjecture,[],[f20])).
% 7.22/1.50  
% 7.22/1.50  fof(f45,plain,(
% 7.22/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.22/1.50    inference(ennf_transformation,[],[f21])).
% 7.22/1.50  
% 7.22/1.50  fof(f46,plain,(
% 7.22/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.22/1.50    inference(flattening,[],[f45])).
% 7.22/1.50  
% 7.22/1.50  fof(f60,plain,(
% 7.22/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.22/1.50    introduced(choice_axiom,[])).
% 7.22/1.50  
% 7.22/1.50  fof(f59,plain,(
% 7.22/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.22/1.50    introduced(choice_axiom,[])).
% 7.22/1.50  
% 7.22/1.50  fof(f58,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.22/1.50    introduced(choice_axiom,[])).
% 7.22/1.50  
% 7.22/1.50  fof(f57,plain,(
% 7.22/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.22/1.50    introduced(choice_axiom,[])).
% 7.22/1.50  
% 7.22/1.50  fof(f56,plain,(
% 7.22/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.22/1.50    introduced(choice_axiom,[])).
% 7.22/1.50  
% 7.22/1.50  fof(f55,plain,(
% 7.22/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.22/1.50    introduced(choice_axiom,[])).
% 7.22/1.50  
% 7.22/1.50  fof(f61,plain,(
% 7.22/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.22/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f46,f60,f59,f58,f57,f56,f55])).
% 7.22/1.50  
% 7.22/1.50  fof(f98,plain,(
% 7.22/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f2,axiom,(
% 7.22/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f23,plain,(
% 7.22/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.22/1.50    inference(ennf_transformation,[],[f2])).
% 7.22/1.50  
% 7.22/1.50  fof(f64,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.22/1.50    inference(cnf_transformation,[],[f23])).
% 7.22/1.50  
% 7.22/1.50  fof(f4,axiom,(
% 7.22/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f66,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.22/1.50    inference(cnf_transformation,[],[f4])).
% 7.22/1.50  
% 7.22/1.50  fof(f109,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.22/1.50    inference(definition_unfolding,[],[f64,f66])).
% 7.22/1.50  
% 7.22/1.50  fof(f105,plain,(
% 7.22/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f17,axiom,(
% 7.22/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f39,plain,(
% 7.22/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.22/1.50    inference(ennf_transformation,[],[f17])).
% 7.22/1.50  
% 7.22/1.50  fof(f40,plain,(
% 7.22/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.22/1.50    inference(flattening,[],[f39])).
% 7.22/1.50  
% 7.22/1.50  fof(f86,plain,(
% 7.22/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f40])).
% 7.22/1.50  
% 7.22/1.50  fof(f103,plain,(
% 7.22/1.50    v1_funct_1(sK5)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f102,plain,(
% 7.22/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f100,plain,(
% 7.22/1.50    v1_funct_1(sK4)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f18,axiom,(
% 7.22/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f41,plain,(
% 7.22/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.22/1.50    inference(ennf_transformation,[],[f18])).
% 7.22/1.50  
% 7.22/1.50  fof(f42,plain,(
% 7.22/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.22/1.50    inference(flattening,[],[f41])).
% 7.22/1.50  
% 7.22/1.50  fof(f53,plain,(
% 7.22/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.22/1.50    inference(nnf_transformation,[],[f42])).
% 7.22/1.50  
% 7.22/1.50  fof(f54,plain,(
% 7.22/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.22/1.50    inference(flattening,[],[f53])).
% 7.22/1.50  
% 7.22/1.50  fof(f88,plain,(
% 7.22/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f54])).
% 7.22/1.50  
% 7.22/1.50  fof(f113,plain,(
% 7.22/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(equality_resolution,[],[f88])).
% 7.22/1.50  
% 7.22/1.50  fof(f19,axiom,(
% 7.22/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f43,plain,(
% 7.22/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.22/1.50    inference(ennf_transformation,[],[f19])).
% 7.22/1.50  
% 7.22/1.50  fof(f44,plain,(
% 7.22/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.22/1.50    inference(flattening,[],[f43])).
% 7.22/1.50  
% 7.22/1.50  fof(f90,plain,(
% 7.22/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f44])).
% 7.22/1.50  
% 7.22/1.50  fof(f91,plain,(
% 7.22/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f44])).
% 7.22/1.50  
% 7.22/1.50  fof(f92,plain,(
% 7.22/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f44])).
% 7.22/1.50  
% 7.22/1.50  fof(f3,axiom,(
% 7.22/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f24,plain,(
% 7.22/1.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.22/1.50    inference(ennf_transformation,[],[f3])).
% 7.22/1.50  
% 7.22/1.50  fof(f65,plain,(
% 7.22/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f24])).
% 7.22/1.50  
% 7.22/1.50  fof(f94,plain,(
% 7.22/1.50    ~v1_xboole_0(sK1)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f95,plain,(
% 7.22/1.50    ~v1_xboole_0(sK2)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f101,plain,(
% 7.22/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f97,plain,(
% 7.22/1.50    ~v1_xboole_0(sK3)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f104,plain,(
% 7.22/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f12,axiom,(
% 7.22/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f31,plain,(
% 7.22/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.22/1.50    inference(ennf_transformation,[],[f12])).
% 7.22/1.50  
% 7.22/1.50  fof(f32,plain,(
% 7.22/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.22/1.50    inference(flattening,[],[f31])).
% 7.22/1.50  
% 7.22/1.50  fof(f51,plain,(
% 7.22/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.22/1.50    inference(nnf_transformation,[],[f32])).
% 7.22/1.50  
% 7.22/1.50  fof(f78,plain,(
% 7.22/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f51])).
% 7.22/1.50  
% 7.22/1.50  fof(f99,plain,(
% 7.22/1.50    r1_subset_1(sK2,sK3)),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f1,axiom,(
% 7.22/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f47,plain,(
% 7.22/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.22/1.50    inference(nnf_transformation,[],[f1])).
% 7.22/1.50  
% 7.22/1.50  fof(f62,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f47])).
% 7.22/1.50  
% 7.22/1.50  fof(f108,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.22/1.50    inference(definition_unfolding,[],[f62,f66])).
% 7.22/1.50  
% 7.22/1.50  fof(f15,axiom,(
% 7.22/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f35,plain,(
% 7.22/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.22/1.50    inference(ennf_transformation,[],[f15])).
% 7.22/1.50  
% 7.22/1.50  fof(f36,plain,(
% 7.22/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.22/1.50    inference(flattening,[],[f35])).
% 7.22/1.50  
% 7.22/1.50  fof(f83,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f36])).
% 7.22/1.50  
% 7.22/1.50  fof(f14,axiom,(
% 7.22/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f22,plain,(
% 7.22/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.22/1.50    inference(pure_predicate_removal,[],[f14])).
% 7.22/1.50  
% 7.22/1.50  fof(f34,plain,(
% 7.22/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.22/1.50    inference(ennf_transformation,[],[f22])).
% 7.22/1.50  
% 7.22/1.50  fof(f81,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.22/1.50    inference(cnf_transformation,[],[f34])).
% 7.22/1.50  
% 7.22/1.50  fof(f16,axiom,(
% 7.22/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f37,plain,(
% 7.22/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.22/1.50    inference(ennf_transformation,[],[f16])).
% 7.22/1.50  
% 7.22/1.50  fof(f38,plain,(
% 7.22/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(flattening,[],[f37])).
% 7.22/1.50  
% 7.22/1.50  fof(f52,plain,(
% 7.22/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(nnf_transformation,[],[f38])).
% 7.22/1.50  
% 7.22/1.50  fof(f84,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f52])).
% 7.22/1.50  
% 7.22/1.50  fof(f13,axiom,(
% 7.22/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f33,plain,(
% 7.22/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.22/1.50    inference(ennf_transformation,[],[f13])).
% 7.22/1.50  
% 7.22/1.50  fof(f80,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.22/1.50    inference(cnf_transformation,[],[f33])).
% 7.22/1.50  
% 7.22/1.50  fof(f11,axiom,(
% 7.22/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f30,plain,(
% 7.22/1.50    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(ennf_transformation,[],[f11])).
% 7.22/1.50  
% 7.22/1.50  fof(f50,plain,(
% 7.22/1.50    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(nnf_transformation,[],[f30])).
% 7.22/1.50  
% 7.22/1.50  fof(f77,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f50])).
% 7.22/1.50  
% 7.22/1.50  fof(f5,axiom,(
% 7.22/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f25,plain,(
% 7.22/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(ennf_transformation,[],[f5])).
% 7.22/1.50  
% 7.22/1.50  fof(f48,plain,(
% 7.22/1.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(nnf_transformation,[],[f25])).
% 7.22/1.50  
% 7.22/1.50  fof(f67,plain,(
% 7.22/1.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f48])).
% 7.22/1.50  
% 7.22/1.50  fof(f8,axiom,(
% 7.22/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f28,plain,(
% 7.22/1.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 7.22/1.50    inference(ennf_transformation,[],[f8])).
% 7.22/1.50  
% 7.22/1.50  fof(f72,plain,(
% 7.22/1.50    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f28])).
% 7.22/1.50  
% 7.22/1.50  fof(f7,axiom,(
% 7.22/1.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f27,plain,(
% 7.22/1.50    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(ennf_transformation,[],[f7])).
% 7.22/1.50  
% 7.22/1.50  fof(f49,plain,(
% 7.22/1.50    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.22/1.50    inference(nnf_transformation,[],[f27])).
% 7.22/1.50  
% 7.22/1.50  fof(f71,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f49])).
% 7.22/1.50  
% 7.22/1.50  fof(f70,plain,(
% 7.22/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f49])).
% 7.22/1.50  
% 7.22/1.50  fof(f10,axiom,(
% 7.22/1.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f74,plain,(
% 7.22/1.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.22/1.50    inference(cnf_transformation,[],[f10])).
% 7.22/1.50  
% 7.22/1.50  fof(f9,axiom,(
% 7.22/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f29,plain,(
% 7.22/1.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.22/1.50    inference(ennf_transformation,[],[f9])).
% 7.22/1.50  
% 7.22/1.50  fof(f73,plain,(
% 7.22/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f29])).
% 7.22/1.50  
% 7.22/1.50  fof(f6,axiom,(
% 7.22/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 7.22/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.22/1.50  
% 7.22/1.50  fof(f26,plain,(
% 7.22/1.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 7.22/1.50    inference(ennf_transformation,[],[f6])).
% 7.22/1.50  
% 7.22/1.50  fof(f69,plain,(
% 7.22/1.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f26])).
% 7.22/1.50  
% 7.22/1.50  fof(f76,plain,(
% 7.22/1.50    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f50])).
% 7.22/1.50  
% 7.22/1.50  fof(f87,plain,(
% 7.22/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(cnf_transformation,[],[f54])).
% 7.22/1.50  
% 7.22/1.50  fof(f114,plain,(
% 7.22/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.22/1.50    inference(equality_resolution,[],[f87])).
% 7.22/1.50  
% 7.22/1.50  fof(f106,plain,(
% 7.22/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  fof(f96,plain,(
% 7.22/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.22/1.50    inference(cnf_transformation,[],[f61])).
% 7.22/1.50  
% 7.22/1.50  cnf(c_38,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.22/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1429,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_38]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2325,plain,
% 7.22/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.22/1.50      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.22/1.50      inference(cnf_transformation,[],[f109]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1452,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.22/1.50      | k9_subset_1(X1_57,X2_57,X0_57) = k1_setfam_1(k2_tarski(X2_57,X0_57)) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2305,plain,
% 7.22/1.50      ( k9_subset_1(X0_57,X1_57,X2_57) = k1_setfam_1(k2_tarski(X1_57,X2_57))
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1452]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3014,plain,
% 7.22/1.50      ( k9_subset_1(sK0,X0_57,sK3) = k1_setfam_1(k2_tarski(X0_57,sK3)) ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2325,c_2305]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_31,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.22/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1435,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_31]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2319,plain,
% 7.22/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1435]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_23,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.22/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1441,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.22/1.50      | ~ v1_funct_1(X0_57)
% 7.22/1.50      | k2_partfun1(X1_57,X2_57,X0_57,X3_57) = k7_relat_1(X0_57,X3_57) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2314,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,X3_57) = k7_relat_1(X2_57,X3_57)
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.22/1.50      | v1_funct_1(X2_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1441]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3748,plain,
% 7.22/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57)
% 7.22/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2319,c_2314]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_33,negated_conjecture,
% 7.22/1.50      ( v1_funct_1(sK5) ),
% 7.22/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2785,plain,
% 7.22/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.22/1.50      | ~ v1_funct_1(sK5)
% 7.22/1.50      | k2_partfun1(X0_57,X1_57,sK5,X2_57) = k7_relat_1(sK5,X2_57) ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_1441]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3026,plain,
% 7.22/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.22/1.50      | ~ v1_funct_1(sK5)
% 7.22/1.50      | k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_2785]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3885,plain,
% 7.22/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_57) = k7_relat_1(sK5,X0_57) ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_3748,c_33,c_31,c_3026]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_34,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.22/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1432,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_34]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2322,plain,
% 7.22/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1432]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3749,plain,
% 7.22/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57)
% 7.22/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2322,c_2314]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_36,negated_conjecture,
% 7.22/1.50      ( v1_funct_1(sK4) ),
% 7.22/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2790,plain,
% 7.22/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.22/1.50      | ~ v1_funct_1(sK4)
% 7.22/1.50      | k2_partfun1(X0_57,X1_57,sK4,X2_57) = k7_relat_1(sK4,X2_57) ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_1441]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3031,plain,
% 7.22/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.22/1.50      | ~ v1_funct_1(sK4)
% 7.22/1.50      | k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_2790]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3975,plain,
% 7.22/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_57) = k7_relat_1(sK4,X0_57) ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_3749,c_36,c_34,c_3031]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_25,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_29,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_28,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_27,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_241,plain,
% 7.22/1.50      ( ~ v1_funct_1(X3)
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_25,c_29,c_28,c_27]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_242,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_241]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1422,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.22/1.50      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.22/1.50      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.22/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.22/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.22/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.22/1.50      | ~ v1_funct_1(X0_57)
% 7.22/1.50      | ~ v1_funct_1(X3_57)
% 7.22/1.50      | v1_xboole_0(X2_57)
% 7.22/1.50      | v1_xboole_0(X1_57)
% 7.22/1.50      | v1_xboole_0(X4_57)
% 7.22/1.50      | v1_xboole_0(X5_57)
% 7.22/1.50      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X1_57) = X0_57 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_242]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2332,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X0_57) = X2_57
% 7.22/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.22/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.22/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.22/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.22/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.22/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X3_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1422]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.22/1.50      | ~ v1_xboole_0(X1)
% 7.22/1.50      | v1_xboole_0(X0) ),
% 7.22/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1451,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(X1_57))
% 7.22/1.50      | ~ v1_xboole_0(X1_57)
% 7.22/1.50      | v1_xboole_0(X0_57) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2306,plain,
% 7.22/1.50      ( m1_subset_1(X0_57,k1_zfmisc_1(X1_57)) != iProver_top
% 7.22/1.50      | v1_xboole_0(X1_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1451]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2570,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X4_57) = X5_57
% 7.22/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.22/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.22/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.22/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X4_57) = iProver_top ),
% 7.22/1.50      inference(forward_subsumption_resolution,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_2332,c_2306]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_9344,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.22/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.22/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.22/1.50      | v1_funct_1(sK4) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.22/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3975,c_2570]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_42,negated_conjecture,
% 7.22/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_45,plain,
% 7.22/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_41,negated_conjecture,
% 7.22/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.22/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_46,plain,
% 7.22/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_51,plain,
% 7.22/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_35,negated_conjecture,
% 7.22/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f101]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_52,plain,
% 7.22/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_53,plain,
% 7.22/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_13979,plain,
% 7.22/1.50      ( v1_funct_1(X1_57) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.22/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.22/1.50      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_9344,c_45,c_46,c_51,c_52,c_53]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_13980,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),X0_57) = X1_57
% 7.22/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_13979]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_13993,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.22/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.22/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 7.22/1.50      | v1_funct_1(sK5) != iProver_top
% 7.22/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3885,c_13980]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_39,negated_conjecture,
% 7.22/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.22/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_48,plain,
% 7.22/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_54,plain,
% 7.22/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_32,negated_conjecture,
% 7.22/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f104]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_55,plain,
% 7.22/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_56,plain,
% 7.22/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16031,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_13993,c_48,c_54,c_55,c_56]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16041,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3014,c_16031]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16,plain,
% 7.22/1.50      ( ~ r1_subset_1(X0,X1)
% 7.22/1.50      | r1_xboole_0(X0,X1)
% 7.22/1.50      | v1_xboole_0(X0)
% 7.22/1.50      | v1_xboole_0(X1) ),
% 7.22/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_37,negated_conjecture,
% 7.22/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.22/1.50      inference(cnf_transformation,[],[f99]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_571,plain,
% 7.22/1.50      ( r1_xboole_0(X0,X1)
% 7.22/1.50      | v1_xboole_0(X0)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | sK3 != X1
% 7.22/1.50      | sK2 != X0 ),
% 7.22/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_572,plain,
% 7.22/1.50      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.22/1.50      inference(unflattening,[status(thm)],[c_571]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_574,plain,
% 7.22/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_572,c_41,c_39]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1421,plain,
% 7.22/1.50      ( r1_xboole_0(sK2,sK3) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_574]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2333,plain,
% 7.22/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1421]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1,plain,
% 7.22/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.22/1.50      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1453,plain,
% 7.22/1.50      ( ~ r1_xboole_0(X0_57,X1_57)
% 7.22/1.50      | k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2304,plain,
% 7.22/1.50      ( k1_setfam_1(k2_tarski(X0_57,X1_57)) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(X0_57,X1_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1453]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3416,plain,
% 7.22/1.50      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2333,c_2304]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_19,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | v1_partfun1(X0,X1)
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | v1_xboole_0(X2) ),
% 7.22/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_18,plain,
% 7.22/1.50      ( v4_relat_1(X0,X1)
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.22/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_22,plain,
% 7.22/1.50      ( ~ v1_partfun1(X0,X1)
% 7.22/1.50      | ~ v4_relat_1(X0,X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_602,plain,
% 7.22/1.50      ( ~ v1_partfun1(X0,X1)
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(resolution,[status(thm)],[c_18,c_22]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_17,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | v1_relat_1(X0) ),
% 7.22/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_606,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_partfun1(X0,X1)
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_602,c_22,c_18,c_17]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_607,plain,
% 7.22/1.50      ( ~ v1_partfun1(X0,X1)
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_606]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_650,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(resolution,[status(thm)],[c_19,c_607]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_654,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_650,c_22,c_19,c_18,c_17]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_655,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | k1_relat_1(X0) = X1 ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_654]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1419,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.22/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.22/1.50      | ~ v1_funct_1(X0_57)
% 7.22/1.50      | v1_xboole_0(X2_57)
% 7.22/1.50      | k1_relat_1(X0_57) = X1_57 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_655]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2335,plain,
% 7.22/1.50      ( k1_relat_1(X0_57) = X1_57
% 7.22/1.50      | v1_funct_2(X0_57,X1_57,X2_57) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.22/1.50      | v1_funct_1(X0_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X2_57) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1419]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4270,plain,
% 7.22/1.50      ( k1_relat_1(sK4) = sK2
% 7.22/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.22/1.50      | v1_funct_1(sK4) != iProver_top
% 7.22/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2322,c_2335]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2780,plain,
% 7.22/1.50      ( ~ v1_funct_2(sK4,X0_57,X1_57)
% 7.22/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.22/1.50      | ~ v1_funct_1(sK4)
% 7.22/1.50      | v1_xboole_0(X1_57)
% 7.22/1.50      | k1_relat_1(sK4) = X0_57 ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_1419]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3023,plain,
% 7.22/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.22/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.22/1.50      | ~ v1_funct_1(sK4)
% 7.22/1.50      | v1_xboole_0(sK1)
% 7.22/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_2780]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5215,plain,
% 7.22/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_4270,c_42,c_36,c_35,c_34,c_3023]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_13,plain,
% 7.22/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1444,plain,
% 7.22/1.50      ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.22/1.50      | ~ v1_relat_1(X0_57)
% 7.22/1.50      | k7_relat_1(X0_57,X1_57) = k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2311,plain,
% 7.22/1.50      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5234,plain,
% 7.22/1.50      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(sK2,X0_57) != iProver_top
% 7.22/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_5215,c_2311]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1442,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.22/1.50      | v1_relat_1(X0_57) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2698,plain,
% 7.22/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.22/1.50      | v1_relat_1(sK4) ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_1442]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2699,plain,
% 7.22/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.22/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_2698]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5853,plain,
% 7.22/1.50      ( r1_xboole_0(sK2,X0_57) != iProver_top
% 7.22/1.50      | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_5234,c_53,c_2699]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5854,plain,
% 7.22/1.50      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(sK2,X0_57) != iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_5853]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5861,plain,
% 7.22/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2333,c_5854]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2313,plain,
% 7.22/1.50      ( m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57))) != iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1442]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3421,plain,
% 7.22/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2322,c_2313]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5,plain,
% 7.22/1.50      ( r1_tarski(k1_relat_1(X0),X1)
% 7.22/1.50      | ~ v4_relat_1(X0,X1)
% 7.22/1.50      | ~ v1_relat_1(X0) ),
% 7.22/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_9,plain,
% 7.22/1.50      ( ~ r1_tarski(X0,X1)
% 7.22/1.50      | ~ v1_relat_1(X2)
% 7.22/1.50      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 7.22/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_547,plain,
% 7.22/1.50      ( ~ v4_relat_1(X0,X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | ~ v1_relat_1(X2)
% 7.22/1.50      | X3 != X1
% 7.22/1.50      | k9_relat_1(k7_relat_1(X2,X3),X4) = k9_relat_1(X2,X4)
% 7.22/1.50      | k1_relat_1(X0) != X4 ),
% 7.22/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_548,plain,
% 7.22/1.50      ( ~ v4_relat_1(X0,X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | ~ v1_relat_1(X2)
% 7.22/1.50      | k9_relat_1(k7_relat_1(X2,X1),k1_relat_1(X0)) = k9_relat_1(X2,k1_relat_1(X0)) ),
% 7.22/1.50      inference(unflattening,[status(thm)],[c_547]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_584,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | ~ v1_relat_1(X3)
% 7.22/1.50      | k9_relat_1(k7_relat_1(X3,X1),k1_relat_1(X0)) = k9_relat_1(X3,k1_relat_1(X0)) ),
% 7.22/1.50      inference(resolution,[status(thm)],[c_18,c_548]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_588,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ v1_relat_1(X3)
% 7.22/1.50      | k9_relat_1(k7_relat_1(X3,X1),k1_relat_1(X0)) = k9_relat_1(X3,k1_relat_1(X0)) ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_584,c_17]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1420,plain,
% 7.22/1.50      ( ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.22/1.50      | ~ v1_relat_1(X3_57)
% 7.22/1.50      | k9_relat_1(k7_relat_1(X3_57,X1_57),k1_relat_1(X0_57)) = k9_relat_1(X3_57,k1_relat_1(X0_57)) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_588]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2334,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(X0_57,X1_57),k1_relat_1(X2_57)) = k9_relat_1(X0_57,k1_relat_1(X2_57))
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X3_57))) != iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1420]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4143,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(X0_57,sK3),k1_relat_1(sK5)) = k9_relat_1(X0_57,k1_relat_1(sK5))
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2319,c_2334]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4251,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(sK4,sK3),k1_relat_1(sK5)) = k9_relat_1(sK4,k1_relat_1(sK5)) ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3421,c_4143]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4269,plain,
% 7.22/1.50      ( k1_relat_1(sK5) = sK3
% 7.22/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.22/1.50      | v1_funct_1(sK5) != iProver_top
% 7.22/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2319,c_2335]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2775,plain,
% 7.22/1.50      ( ~ v1_funct_2(sK5,X0_57,X1_57)
% 7.22/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57)))
% 7.22/1.50      | ~ v1_funct_1(sK5)
% 7.22/1.50      | v1_xboole_0(X1_57)
% 7.22/1.50      | k1_relat_1(sK5) = X0_57 ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_1419]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3020,plain,
% 7.22/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.22/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.22/1.50      | ~ v1_funct_1(sK5)
% 7.22/1.50      | v1_xboole_0(sK1)
% 7.22/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_2775]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4881,plain,
% 7.22/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_4269,c_42,c_33,c_32,c_31,c_3020]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5451,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(sK4,sK3),sK3) = k9_relat_1(sK4,sK3) ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_4251,c_4881]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5940,plain,
% 7.22/1.50      ( k9_relat_1(k1_xboole_0,sK3) = k9_relat_1(sK4,sK3) ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_5861,c_5451]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_7,plain,
% 7.22/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1449,plain,
% 7.22/1.50      ( ~ r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.22/1.50      | ~ v1_relat_1(X0_57)
% 7.22/1.50      | k9_relat_1(X0_57,X1_57) = k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2308,plain,
% 7.22/1.50      ( k9_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(k1_relat_1(X0_57),X1_57) != iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1449]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5236,plain,
% 7.22/1.50      ( k9_relat_1(sK4,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(sK2,X0_57) != iProver_top
% 7.22/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_5215,c_2308]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6199,plain,
% 7.22/1.50      ( r1_xboole_0(sK2,X0_57) != iProver_top
% 7.22/1.50      | k9_relat_1(sK4,X0_57) = k1_xboole_0 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_5236,c_53,c_2699]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6200,plain,
% 7.22/1.50      ( k9_relat_1(sK4,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(sK2,X0_57) != iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_6199]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6207,plain,
% 7.22/1.50      ( k9_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2333,c_6200]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6967,plain,
% 7.22/1.50      ( k9_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_5940,c_6207]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_8,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1448,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.22/1.50      | ~ v1_relat_1(X0_57)
% 7.22/1.50      | k9_relat_1(X0_57,X1_57) != k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2309,plain,
% 7.22/1.50      ( k9_relat_1(X0_57,X1_57) != k1_xboole_0
% 7.22/1.50      | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6969,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK3) = iProver_top
% 7.22/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_6967,c_2309]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_12,plain,
% 7.22/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1445,plain,
% 7.22/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6970,plain,
% 7.22/1.50      ( r1_xboole_0(k1_xboole_0,sK3) = iProver_top
% 7.22/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_6969,c_1445]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2695,plain,
% 7.22/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.22/1.50      | v1_relat_1(sK5) ),
% 7.22/1.50      inference(instantiation,[status(thm)],[c_1442]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2696,plain,
% 7.22/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.22/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_2695]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10,plain,
% 7.22/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.22/1.50      | ~ v1_relat_1(X1)
% 7.22/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1447,plain,
% 7.22/1.50      ( ~ r1_xboole_0(X0_57,k1_relat_1(X1_57))
% 7.22/1.50      | ~ v1_relat_1(X1_57)
% 7.22/1.50      | k7_relat_1(X1_57,X0_57) = k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2310,plain,
% 7.22/1.50      ( k7_relat_1(X0_57,X1_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(X1_57,k1_relat_1(X0_57)) != iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1447]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4901,plain,
% 7.22/1.50      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(X0_57,sK3) != iProver_top
% 7.22/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_4881,c_2310]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5772,plain,
% 7.22/1.50      ( r1_xboole_0(X0_57,sK3) != iProver_top
% 7.22/1.50      | k7_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_4901,c_56,c_2696]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5773,plain,
% 7.22/1.50      ( k7_relat_1(sK5,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(X0_57,sK3) != iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_5772]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5780,plain,
% 7.22/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2333,c_5773]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6,plain,
% 7.22/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 7.22/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1450,plain,
% 7.22/1.50      ( ~ v1_relat_1(X0_57) | v1_relat_1(k7_relat_1(X0_57,X1_57)) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2307,plain,
% 7.22/1.50      ( v1_relat_1(X0_57) != iProver_top
% 7.22/1.50      | v1_relat_1(k7_relat_1(X0_57,X1_57)) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1450]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5865,plain,
% 7.22/1.50      ( v1_relat_1(sK5) != iProver_top
% 7.22/1.50      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_5780,c_2307]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_7507,plain,
% 7.22/1.50      ( r1_xboole_0(k1_xboole_0,sK3) = iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_6970,c_56,c_2696,c_5865]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_7513,plain,
% 7.22/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_7507,c_5773]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16042,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_16041,c_3416,c_7513]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16043,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_16042,c_3014]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3420,plain,
% 7.22/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2319,c_2313]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4144,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(X0_57,sK2),k1_relat_1(sK4)) = k9_relat_1(X0_57,k1_relat_1(sK4))
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_2322,c_2334]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4424,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(sK5,sK2),k1_relat_1(sK4)) = k9_relat_1(sK5,k1_relat_1(sK4)) ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3420,c_4144]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5455,plain,
% 7.22/1.50      ( k9_relat_1(k7_relat_1(sK5,sK2),sK2) = k9_relat_1(sK5,sK2) ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_4424,c_5215]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5863,plain,
% 7.22/1.50      ( k9_relat_1(k1_xboole_0,sK2) = k9_relat_1(sK5,sK2) ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_5780,c_5455]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_14,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.22/1.50      | ~ v1_relat_1(X0)
% 7.22/1.50      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 7.22/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1443,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(X0_57),X1_57)
% 7.22/1.50      | ~ v1_relat_1(X0_57)
% 7.22/1.50      | k7_relat_1(X0_57,X1_57) != k1_xboole_0 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2312,plain,
% 7.22/1.50      ( k7_relat_1(X0_57,X1_57) != k1_xboole_0
% 7.22/1.50      | r1_xboole_0(k1_relat_1(X0_57),X1_57) = iProver_top
% 7.22/1.50      | v1_relat_1(X0_57) != iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5864,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(sK5),sK2) = iProver_top
% 7.22/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_5780,c_2312]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5880,plain,
% 7.22/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top
% 7.22/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_5864,c_4881]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5955,plain,
% 7.22/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_5880,c_56,c_2696]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_4902,plain,
% 7.22/1.50      ( k9_relat_1(sK5,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(sK3,X0_57) != iProver_top
% 7.22/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_4881,c_2308]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5782,plain,
% 7.22/1.50      ( r1_xboole_0(sK3,X0_57) != iProver_top
% 7.22/1.50      | k9_relat_1(sK5,X0_57) = k1_xboole_0 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_4902,c_56,c_2696]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5783,plain,
% 7.22/1.50      ( k9_relat_1(sK5,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(sK3,X0_57) != iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_5782]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5961,plain,
% 7.22/1.50      ( k9_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_5955,c_5783]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6861,plain,
% 7.22/1.50      ( k9_relat_1(k1_xboole_0,sK2) = k1_xboole_0 ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_5863,c_5961]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6863,plain,
% 7.22/1.50      ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) = iProver_top
% 7.22/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_6861,c_2309]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6864,plain,
% 7.22/1.50      ( r1_xboole_0(k1_xboole_0,sK2) = iProver_top
% 7.22/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,[status(thm)],[c_6863,c_1445]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_7488,plain,
% 7.22/1.50      ( r1_xboole_0(k1_xboole_0,sK2) = iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_6864,c_56,c_2696,c_5865]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_5235,plain,
% 7.22/1.50      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(X0_57,sK2) != iProver_top
% 7.22/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_5215,c_2310]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6081,plain,
% 7.22/1.50      ( r1_xboole_0(X0_57,sK2) != iProver_top
% 7.22/1.50      | k7_relat_1(sK4,X0_57) = k1_xboole_0 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_5235,c_53,c_2699]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_6082,plain,
% 7.22/1.50      ( k7_relat_1(sK4,X0_57) = k1_xboole_0
% 7.22/1.50      | r1_xboole_0(X0_57,sK2) != iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_6081]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_7496,plain,
% 7.22/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_7488,c_6082]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16044,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | k1_xboole_0 != k1_xboole_0
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_16043,c_3416,c_7496]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_16045,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(equality_resolution_simp,[status(thm)],[c_16044]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_26,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.22/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_234,plain,
% 7.22/1.50      ( ~ v1_funct_1(X3)
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_26,c_29,c_28,c_27]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_235,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.22/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.22/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.22/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.22/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.22/1.50      | ~ v1_funct_1(X0)
% 7.22/1.50      | ~ v1_funct_1(X3)
% 7.22/1.50      | v1_xboole_0(X1)
% 7.22/1.50      | v1_xboole_0(X2)
% 7.22/1.50      | v1_xboole_0(X4)
% 7.22/1.50      | v1_xboole_0(X5)
% 7.22/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_234]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1423,plain,
% 7.22/1.50      ( ~ v1_funct_2(X0_57,X1_57,X2_57)
% 7.22/1.50      | ~ v1_funct_2(X3_57,X4_57,X2_57)
% 7.22/1.50      | ~ m1_subset_1(X4_57,k1_zfmisc_1(X5_57))
% 7.22/1.50      | ~ m1_subset_1(X1_57,k1_zfmisc_1(X5_57))
% 7.22/1.50      | ~ m1_subset_1(X0_57,k1_zfmisc_1(k2_zfmisc_1(X1_57,X2_57)))
% 7.22/1.50      | ~ m1_subset_1(X3_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X2_57)))
% 7.22/1.50      | ~ v1_funct_1(X0_57)
% 7.22/1.50      | ~ v1_funct_1(X3_57)
% 7.22/1.50      | v1_xboole_0(X2_57)
% 7.22/1.50      | v1_xboole_0(X1_57)
% 7.22/1.50      | v1_xboole_0(X4_57)
% 7.22/1.50      | v1_xboole_0(X5_57)
% 7.22/1.50      | k2_partfun1(X1_57,X2_57,X0_57,k9_subset_1(X5_57,X4_57,X1_57)) != k2_partfun1(X4_57,X2_57,X3_57,k9_subset_1(X5_57,X4_57,X1_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X5_57,X4_57,X1_57),X2_57,k1_tmap_1(X5_57,X2_57,X4_57,X1_57,X3_57,X0_57),X4_57) = X3_57 ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_235]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2331,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X4_57,X0_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X4_57,X0_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X3_57,X4_57,X0_57),X1_57,k1_tmap_1(X3_57,X1_57,X4_57,X0_57,X5_57,X2_57),X4_57) = X5_57
% 7.22/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.22/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.22/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.22/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.22/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.22/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X3_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X4_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_1423]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_2542,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,X1_57,X2_57,k9_subset_1(X3_57,X0_57,X4_57)) != k2_partfun1(X4_57,X1_57,X5_57,k9_subset_1(X3_57,X0_57,X4_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X3_57,X0_57,X4_57),X1_57,k1_tmap_1(X3_57,X1_57,X0_57,X4_57,X2_57,X5_57),X0_57) = X2_57
% 7.22/1.50      | v1_funct_2(X5_57,X4_57,X1_57) != iProver_top
% 7.22/1.50      | v1_funct_2(X2_57,X0_57,X1_57) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X4_57,k1_zfmisc_1(X3_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X5_57,k1_zfmisc_1(k2_zfmisc_1(X4_57,X1_57))) != iProver_top
% 7.22/1.50      | m1_subset_1(X2_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,X1_57))) != iProver_top
% 7.22/1.50      | v1_funct_1(X5_57) != iProver_top
% 7.22/1.50      | v1_funct_1(X2_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X1_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(X4_57) = iProver_top ),
% 7.22/1.50      inference(forward_subsumption_resolution,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_2331,c_2306]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_8283,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 7.22/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.22/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.22/1.50      | v1_funct_1(sK4) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top
% 7.22/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.22/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3975,c_2542]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_9195,plain,
% 7.22/1.50      ( v1_funct_1(X1_57) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.22/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 7.22/1.50      | k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_8283,c_45,c_46,c_51,c_52,c_53]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_9196,plain,
% 7.22/1.50      ( k2_partfun1(X0_57,sK1,X1_57,k9_subset_1(X2_57,sK2,X0_57)) != k7_relat_1(sK4,k9_subset_1(X2_57,sK2,X0_57))
% 7.22/1.50      | k2_partfun1(k4_subset_1(X2_57,sK2,X0_57),sK1,k1_tmap_1(X2_57,sK1,sK2,X0_57,sK4,X1_57),sK2) = sK4
% 7.22/1.50      | v1_funct_2(X1_57,X0_57,sK1) != iProver_top
% 7.22/1.50      | m1_subset_1(X0_57,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(X1_57,k1_zfmisc_1(k2_zfmisc_1(X0_57,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_57)) != iProver_top
% 7.22/1.50      | v1_funct_1(X1_57) != iProver_top
% 7.22/1.50      | v1_xboole_0(X0_57) = iProver_top ),
% 7.22/1.50      inference(renaming,[status(thm)],[c_9195]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_9209,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.22/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.22/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top
% 7.22/1.50      | v1_funct_1(sK5) != iProver_top
% 7.22/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3885,c_9196]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10043,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(X0_57,sK2,sK3),sK1,k1_tmap_1(X0_57,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | k7_relat_1(sK4,k9_subset_1(X0_57,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_57,sK2,sK3))
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_57)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_57)) != iProver_top ),
% 7.22/1.50      inference(global_propositional_subsumption,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_9209,c_48,c_54,c_55,c_56]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10053,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(superposition,[status(thm)],[c_3014,c_10043]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10054,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_10053,c_3416,c_7513]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10055,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k1_xboole_0
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_10054,c_3014]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10056,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | k1_xboole_0 != k1_xboole_0
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(light_normalisation,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_10055,c_3416,c_7496]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_10057,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.22/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.22/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.22/1.50      inference(equality_resolution_simp,[status(thm)],[c_10056]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_30,negated_conjecture,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.22/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_1436,negated_conjecture,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.22/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3192,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_3014,c_1436]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3569,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_3416,c_3192]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3889,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_3885,c_3569]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_3979,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_3889,c_3975]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_7636,plain,
% 7.22/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.22/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.22/1.50      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 7.22/1.50      inference(demodulation,[status(thm)],[c_7496,c_3979]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_49,plain,
% 7.22/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_40,negated_conjecture,
% 7.22/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.22/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(c_47,plain,
% 7.22/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.22/1.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.22/1.50  
% 7.22/1.50  cnf(contradiction,plain,
% 7.22/1.50      ( $false ),
% 7.22/1.50      inference(minisat,
% 7.22/1.50                [status(thm)],
% 7.22/1.50                [c_16045,c_10057,c_7636,c_7513,c_49,c_47]) ).
% 7.22/1.50  
% 7.22/1.50  
% 7.22/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.22/1.50  
% 7.22/1.50  ------                               Statistics
% 7.22/1.50  
% 7.22/1.50  ------ General
% 7.22/1.50  
% 7.22/1.50  abstr_ref_over_cycles:                  0
% 7.22/1.50  abstr_ref_under_cycles:                 0
% 7.22/1.50  gc_basic_clause_elim:                   0
% 7.22/1.50  forced_gc_time:                         0
% 7.22/1.50  parsing_time:                           0.011
% 7.22/1.50  unif_index_cands_time:                  0.
% 7.22/1.50  unif_index_add_time:                    0.
% 7.22/1.50  orderings_time:                         0.
% 7.22/1.50  out_proof_time:                         0.018
% 7.22/1.50  total_time:                             0.778
% 7.22/1.50  num_of_symbols:                         63
% 7.22/1.50  num_of_terms:                           34489
% 7.22/1.50  
% 7.22/1.50  ------ Preprocessing
% 7.22/1.50  
% 7.22/1.50  num_of_splits:                          0
% 7.22/1.50  num_of_split_atoms:                     0
% 7.22/1.50  num_of_reused_defs:                     0
% 7.22/1.50  num_eq_ax_congr_red:                    16
% 7.22/1.50  num_of_sem_filtered_clauses:            1
% 7.22/1.50  num_of_subtypes:                        3
% 7.22/1.50  monotx_restored_types:                  0
% 7.22/1.50  sat_num_of_epr_types:                   0
% 7.22/1.50  sat_num_of_non_cyclic_types:            0
% 7.22/1.50  sat_guarded_non_collapsed_types:        1
% 7.22/1.50  num_pure_diseq_elim:                    0
% 7.22/1.50  simp_replaced_by:                       0
% 7.22/1.50  res_preprocessed:                       192
% 7.22/1.50  prep_upred:                             0
% 7.22/1.50  prep_unflattend:                        46
% 7.22/1.50  smt_new_axioms:                         0
% 7.22/1.50  pred_elim_cands:                        6
% 7.22/1.50  pred_elim:                              4
% 7.22/1.50  pred_elim_cl:                           7
% 7.22/1.50  pred_elim_cycles:                       6
% 7.22/1.50  merged_defs:                            8
% 7.22/1.50  merged_defs_ncl:                        0
% 7.22/1.50  bin_hyper_res:                          8
% 7.22/1.50  prep_cycles:                            4
% 7.22/1.50  pred_elim_time:                         0.016
% 7.22/1.50  splitting_time:                         0.
% 7.22/1.50  sem_filter_time:                        0.
% 7.22/1.50  monotx_time:                            0.
% 7.22/1.50  subtype_inf_time:                       0.001
% 7.22/1.50  
% 7.22/1.50  ------ Problem properties
% 7.22/1.50  
% 7.22/1.50  clauses:                                36
% 7.22/1.50  conjectures:                            13
% 7.22/1.50  epr:                                    9
% 7.22/1.50  horn:                                   29
% 7.22/1.50  ground:                                 16
% 7.22/1.50  unary:                                  15
% 7.22/1.50  binary:                                 5
% 7.22/1.50  lits:                                   141
% 7.22/1.50  lits_eq:                                22
% 7.22/1.50  fd_pure:                                0
% 7.22/1.50  fd_pseudo:                              0
% 7.22/1.50  fd_cond:                                0
% 7.22/1.50  fd_pseudo_cond:                         1
% 7.22/1.50  ac_symbols:                             0
% 7.22/1.50  
% 7.22/1.50  ------ Propositional Solver
% 7.22/1.50  
% 7.22/1.50  prop_solver_calls:                      30
% 7.22/1.50  prop_fast_solver_calls:                 2293
% 7.22/1.50  smt_solver_calls:                       0
% 7.22/1.50  smt_fast_solver_calls:                  0
% 7.22/1.50  prop_num_of_clauses:                    7477
% 7.22/1.50  prop_preprocess_simplified:             16629
% 7.22/1.50  prop_fo_subsumed:                       108
% 7.22/1.50  prop_solver_time:                       0.
% 7.22/1.50  smt_solver_time:                        0.
% 7.22/1.50  smt_fast_solver_time:                   0.
% 7.22/1.50  prop_fast_solver_time:                  0.
% 7.22/1.50  prop_unsat_core_time:                   0.001
% 7.22/1.50  
% 7.22/1.50  ------ QBF
% 7.22/1.50  
% 7.22/1.50  qbf_q_res:                              0
% 7.22/1.50  qbf_num_tautologies:                    0
% 7.22/1.50  qbf_prep_cycles:                        0
% 7.22/1.50  
% 7.22/1.50  ------ BMC1
% 7.22/1.50  
% 7.22/1.50  bmc1_current_bound:                     -1
% 7.22/1.50  bmc1_last_solved_bound:                 -1
% 7.22/1.50  bmc1_unsat_core_size:                   -1
% 7.22/1.50  bmc1_unsat_core_parents_size:           -1
% 7.22/1.50  bmc1_merge_next_fun:                    0
% 7.22/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.22/1.50  
% 7.22/1.50  ------ Instantiation
% 7.22/1.50  
% 7.22/1.50  inst_num_of_clauses:                    1910
% 7.22/1.50  inst_num_in_passive:                    1151
% 7.22/1.50  inst_num_in_active:                     757
% 7.22/1.50  inst_num_in_unprocessed:                2
% 7.22/1.50  inst_num_of_loops:                      780
% 7.22/1.50  inst_num_of_learning_restarts:          0
% 7.22/1.50  inst_num_moves_active_passive:          17
% 7.22/1.50  inst_lit_activity:                      0
% 7.22/1.50  inst_lit_activity_moves:                0
% 7.22/1.50  inst_num_tautologies:                   0
% 7.22/1.50  inst_num_prop_implied:                  0
% 7.22/1.50  inst_num_existing_simplified:           0
% 7.22/1.50  inst_num_eq_res_simplified:             0
% 7.22/1.50  inst_num_child_elim:                    0
% 7.22/1.50  inst_num_of_dismatching_blockings:      221
% 7.22/1.50  inst_num_of_non_proper_insts:           1382
% 7.22/1.50  inst_num_of_duplicates:                 0
% 7.22/1.50  inst_inst_num_from_inst_to_res:         0
% 7.22/1.50  inst_dismatching_checking_time:         0.
% 7.22/1.50  
% 7.22/1.50  ------ Resolution
% 7.22/1.50  
% 7.22/1.50  res_num_of_clauses:                     0
% 7.22/1.50  res_num_in_passive:                     0
% 7.22/1.50  res_num_in_active:                      0
% 7.22/1.50  res_num_of_loops:                       196
% 7.22/1.50  res_forward_subset_subsumed:            46
% 7.22/1.50  res_backward_subset_subsumed:           4
% 7.22/1.50  res_forward_subsumed:                   0
% 7.22/1.50  res_backward_subsumed:                  0
% 7.22/1.50  res_forward_subsumption_resolution:     1
% 7.22/1.50  res_backward_subsumption_resolution:    0
% 7.22/1.50  res_clause_to_clause_subsumption:       744
% 7.22/1.50  res_orphan_elimination:                 0
% 7.22/1.50  res_tautology_del:                      80
% 7.22/1.50  res_num_eq_res_simplified:              0
% 7.22/1.50  res_num_sel_changes:                    0
% 7.22/1.50  res_moves_from_active_to_pass:          0
% 7.22/1.50  
% 7.22/1.50  ------ Superposition
% 7.22/1.50  
% 7.22/1.50  sup_time_total:                         0.
% 7.22/1.50  sup_time_generating:                    0.
% 7.22/1.50  sup_time_sim_full:                      0.
% 7.22/1.50  sup_time_sim_immed:                     0.
% 7.22/1.50  
% 7.22/1.50  sup_num_of_clauses:                     209
% 7.22/1.50  sup_num_in_active:                      143
% 7.22/1.50  sup_num_in_passive:                     66
% 7.22/1.50  sup_num_of_loops:                       154
% 7.22/1.50  sup_fw_superposition:                   191
% 7.22/1.50  sup_bw_superposition:                   91
% 7.22/1.50  sup_immediate_simplified:               117
% 7.22/1.50  sup_given_eliminated:                   0
% 7.22/1.50  comparisons_done:                       0
% 7.22/1.50  comparisons_avoided:                    0
% 7.22/1.50  
% 7.22/1.50  ------ Simplifications
% 7.22/1.50  
% 7.22/1.50  
% 7.22/1.50  sim_fw_subset_subsumed:                 8
% 7.22/1.50  sim_bw_subset_subsumed:                 0
% 7.22/1.50  sim_fw_subsumed:                        3
% 7.22/1.50  sim_bw_subsumed:                        0
% 7.22/1.50  sim_fw_subsumption_res:                 6
% 7.22/1.50  sim_bw_subsumption_res:                 0
% 7.22/1.50  sim_tautology_del:                      2
% 7.22/1.50  sim_eq_tautology_del:                   5
% 7.22/1.50  sim_eq_res_simp:                        16
% 7.22/1.50  sim_fw_demodulated:                     29
% 7.22/1.50  sim_bw_demodulated:                     12
% 7.22/1.50  sim_light_normalised:                   113
% 7.22/1.50  sim_joinable_taut:                      0
% 7.22/1.50  sim_joinable_simp:                      0
% 7.22/1.50  sim_ac_normalised:                      0
% 7.22/1.50  sim_smt_subsumption:                    0
% 7.22/1.50  
%------------------------------------------------------------------------------
