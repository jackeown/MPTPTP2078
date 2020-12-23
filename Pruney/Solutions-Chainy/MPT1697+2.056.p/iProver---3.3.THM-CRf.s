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
% DateTime   : Thu Dec  3 12:21:34 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  194 (3135 expanded)
%              Number of clauses        :  129 ( 748 expanded)
%              Number of leaves         :   16 (1290 expanded)
%              Depth                    :   28
%              Number of atoms          : 1168 (43973 expanded)
%              Number of equality atoms :  490 (10522 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f45,f44,f43,f42,f41,f40])).

fof(f80,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
    inference(flattening,[],[f38])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
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
    inference(equality_resolution,[],[f62])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_911,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1366,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_911])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1360,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_918])).

cnf(c_2319,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1360])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_920,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_250,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_567,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(X3,X2) != k1_xboole_0
    | k1_relat_1(X0) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_250,c_4])).

cnf(c_568,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(X0),X1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_896,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(X0_53),X1_53) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_568])).

cnf(c_1381,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | k3_xboole_0(k1_relat_1(X0_53),X1_53) != k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_10438,plain,
    ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_920,c_1381])).

cnf(c_10499,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2319,c_10438])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_905,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1372,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_905])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1359,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_2385,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1372,c_1359])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_908,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1369,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_908])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_917,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1361,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_917])).

cnf(c_2420,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_1361])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2819,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2420,c_42])).

cnf(c_2419,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1361])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2776,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2419,c_45])).

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
    inference(cnf_transformation,[],[f85])).

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
    inference(cnf_transformation,[],[f65])).

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
    inference(cnf_transformation,[],[f66])).

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
    inference(cnf_transformation,[],[f67])).

cnf(c_195,plain,
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

cnf(c_196,plain,
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
    inference(renaming,[status(thm)],[c_195])).

cnf(c_898,plain,
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
    inference(subtyping,[status(esa)],[c_196])).

cnf(c_1379,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_898])).

cnf(c_4216,plain,
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
    inference(superposition,[status(thm)],[c_2776,c_1379])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8034,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4216,c_36,c_39,c_45,c_46,c_47])).

cnf(c_8035,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_8034])).

cnf(c_8041,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_8035])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8067,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8041,c_37,c_42,c_43,c_44])).

cnf(c_8068,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_8067])).

cnf(c_8073,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_8068])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_252,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_520,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_521,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_523,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_32,c_30])).

cnf(c_597,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_523])).

cnf(c_598,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_894,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_598])).

cnf(c_8074,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8073,c_894])).

cnf(c_913,plain,
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
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1365,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_913])).

cnf(c_915,plain,
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
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1363,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_915])).

cnf(c_2561,plain,
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
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1363,c_1361])).

cnf(c_4369,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_2561])).

cnf(c_4374,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_4369])).

cnf(c_4429,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4374,c_36,c_39,c_45,c_46])).

cnf(c_4430,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_4429])).

cnf(c_4436,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_4430])).

cnf(c_4530,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4436,c_37,c_42,c_43])).

cnf(c_4531,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_4530])).

cnf(c_4536,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_4531])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4546,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4536,c_35,c_38])).

cnf(c_8075,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8074,c_2385,c_4546])).

cnf(c_8076,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8075,c_894])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_912,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2416,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2385,c_912])).

cnf(c_2417,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2416,c_894])).

cnf(c_2822,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2417,c_2776,c_2819])).

cnf(c_4549,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4546,c_2822])).

cnf(c_4550,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4549,c_4546])).

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
    inference(cnf_transformation,[],[f86])).

cnf(c_188,plain,
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

cnf(c_189,plain,
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
    inference(renaming,[status(thm)],[c_188])).

cnf(c_899,plain,
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
    inference(subtyping,[status(esa)],[c_189])).

cnf(c_1378,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_3811,plain,
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
    inference(superposition,[status(thm)],[c_2776,c_1378])).

cnf(c_4985,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3811,c_36,c_39,c_45,c_46,c_47])).

cnf(c_4986,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_4985])).

cnf(c_4992,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2819,c_4986])).

cnf(c_5106,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4992,c_37,c_42,c_43,c_44])).

cnf(c_5107,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_5106])).

cnf(c_5112,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2385,c_5107])).

cnf(c_5113,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5112,c_894])).

cnf(c_5114,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5113,c_2385,c_4546])).

cnf(c_5115,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5114,c_894])).

cnf(c_5116,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5115])).

cnf(c_5221,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5115,c_34,c_31,c_29,c_5116])).

cnf(c_5222,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_5221])).

cnf(c_8077,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8076])).

cnf(c_8095,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8076,c_34,c_31,c_29,c_4550,c_5222,c_8077])).

cnf(c_10506,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10499,c_8095])).

cnf(c_2320,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_1360])).

cnf(c_10500,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2320,c_10438])).

cnf(c_10508,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10506,c_10500])).

cnf(c_10509,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10508])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.76/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.49  
% 7.76/1.49  ------  iProver source info
% 7.76/1.49  
% 7.76/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.49  git: non_committed_changes: false
% 7.76/1.49  git: last_make_outside_of_git: false
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    ""
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             all
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         305.
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              default
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           true
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             true
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         true
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     num_symb
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       true
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.49  --res_passive_queues_freq               [15;5]
% 7.76/1.49  --res_forward_subs                      full
% 7.76/1.49  --res_backward_subs                     full
% 7.76/1.49  --res_forward_subs_resolution           true
% 7.76/1.49  --res_backward_subs_resolution          true
% 7.76/1.49  --res_orphan_elimination                true
% 7.76/1.49  --res_time_limit                        2.
% 7.76/1.49  --res_out_proof                         true
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Options
% 7.76/1.49  
% 7.76/1.49  --superposition_flag                    true
% 7.76/1.49  --sup_passive_queue_type                priority_queues
% 7.76/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.49  --demod_completeness_check              fast
% 7.76/1.49  --demod_use_ground                      true
% 7.76/1.49  --sup_to_prop_solver                    passive
% 7.76/1.49  --sup_prop_simpl_new                    true
% 7.76/1.49  --sup_prop_simpl_given                  true
% 7.76/1.49  --sup_fun_splitting                     true
% 7.76/1.49  --sup_smt_interval                      50000
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Simplification Setup
% 7.76/1.49  
% 7.76/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.49  --sup_immed_triv                        [TrivRules]
% 7.76/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_bw_main                     []
% 7.76/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_input_bw                          []
% 7.76/1.49  
% 7.76/1.49  ------ Combination Options
% 7.76/1.49  
% 7.76/1.49  --comb_res_mult                         3
% 7.76/1.49  --comb_sup_mult                         2
% 7.76/1.49  --comb_inst_mult                        10
% 7.76/1.49  
% 7.76/1.49  ------ Debug Options
% 7.76/1.49  
% 7.76/1.49  --dbg_backtrace                         false
% 7.76/1.49  --dbg_dump_prop_clauses                 false
% 7.76/1.49  --dbg_dump_prop_clauses_file            -
% 7.76/1.49  --dbg_out_stat                          false
% 7.76/1.49  ------ Parsing...
% 7.76/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.49  ------ Proving...
% 7.76/1.49  ------ Problem Properties 
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  clauses                                 28
% 7.76/1.49  conjectures                             13
% 7.76/1.49  EPR                                     8
% 7.76/1.49  Horn                                    21
% 7.76/1.49  unary                                   14
% 7.76/1.49  binary                                  2
% 7.76/1.49  lits                                    122
% 7.76/1.49  lits eq                                 20
% 7.76/1.49  fd_pure                                 0
% 7.76/1.49  fd_pseudo                               0
% 7.76/1.49  fd_cond                                 0
% 7.76/1.49  fd_pseudo_cond                          1
% 7.76/1.49  AC symbols                              0
% 7.76/1.49  
% 7.76/1.49  ------ Schedule dynamic 5 is on 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  Current options:
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    ""
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             all
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         305.
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              default
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           true
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             true
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         true
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     none
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       false
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.49  --res_passive_queues_freq               [15;5]
% 7.76/1.49  --res_forward_subs                      full
% 7.76/1.49  --res_backward_subs                     full
% 7.76/1.49  --res_forward_subs_resolution           true
% 7.76/1.49  --res_backward_subs_resolution          true
% 7.76/1.49  --res_orphan_elimination                true
% 7.76/1.49  --res_time_limit                        2.
% 7.76/1.49  --res_out_proof                         true
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Options
% 7.76/1.49  
% 7.76/1.49  --superposition_flag                    true
% 7.76/1.49  --sup_passive_queue_type                priority_queues
% 7.76/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.49  --demod_completeness_check              fast
% 7.76/1.49  --demod_use_ground                      true
% 7.76/1.49  --sup_to_prop_solver                    passive
% 7.76/1.49  --sup_prop_simpl_new                    true
% 7.76/1.49  --sup_prop_simpl_given                  true
% 7.76/1.49  --sup_fun_splitting                     true
% 7.76/1.49  --sup_smt_interval                      50000
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Simplification Setup
% 7.76/1.49  
% 7.76/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.76/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.76/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.76/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.76/1.49  --sup_immed_triv                        [TrivRules]
% 7.76/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_bw_main                     []
% 7.76/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.76/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_input_bw                          []
% 7.76/1.49  
% 7.76/1.49  ------ Combination Options
% 7.76/1.49  
% 7.76/1.49  --comb_res_mult                         3
% 7.76/1.49  --comb_sup_mult                         2
% 7.76/1.49  --comb_inst_mult                        10
% 7.76/1.49  
% 7.76/1.49  ------ Debug Options
% 7.76/1.49  
% 7.76/1.49  --dbg_backtrace                         false
% 7.76/1.49  --dbg_dump_prop_clauses                 false
% 7.76/1.49  --dbg_dump_prop_clauses_file            -
% 7.76/1.49  --dbg_out_stat                          false
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  ------ Proving...
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  % SZS status Theorem for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49   Resolution empty clause
% 7.76/1.49  
% 7.76/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  fof(f13,conjecture,(
% 7.76/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f14,negated_conjecture,(
% 7.76/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.76/1.49    inference(negated_conjecture,[],[f13])).
% 7.76/1.49  
% 7.76/1.49  fof(f32,plain,(
% 7.76/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.76/1.49    inference(ennf_transformation,[],[f14])).
% 7.76/1.49  
% 7.76/1.49  fof(f33,plain,(
% 7.76/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.76/1.49    inference(flattening,[],[f32])).
% 7.76/1.49  
% 7.76/1.49  fof(f45,plain,(
% 7.76/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f44,plain,(
% 7.76/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f43,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f42,plain,(
% 7.76/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f41,plain,(
% 7.76/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f40,plain,(
% 7.76/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f46,plain,(
% 7.76/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.76/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f45,f44,f43,f42,f41,f40])).
% 7.76/1.49  
% 7.76/1.49  fof(f80,plain,(
% 7.76/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f6,axiom,(
% 7.76/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f20,plain,(
% 7.76/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.76/1.49    inference(ennf_transformation,[],[f6])).
% 7.76/1.49  
% 7.76/1.49  fof(f55,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f20])).
% 7.76/1.49  
% 7.76/1.49  fof(f2,axiom,(
% 7.76/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f49,plain,(
% 7.76/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f2])).
% 7.76/1.49  
% 7.76/1.49  fof(f1,axiom,(
% 7.76/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f34,plain,(
% 7.76/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.76/1.49    inference(nnf_transformation,[],[f1])).
% 7.76/1.49  
% 7.76/1.49  fof(f48,plain,(
% 7.76/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f34])).
% 7.76/1.49  
% 7.76/1.49  fof(f4,axiom,(
% 7.76/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f17,plain,(
% 7.76/1.49    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.76/1.49    inference(ennf_transformation,[],[f4])).
% 7.76/1.49  
% 7.76/1.49  fof(f35,plain,(
% 7.76/1.49    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.76/1.49    inference(nnf_transformation,[],[f17])).
% 7.76/1.49  
% 7.76/1.49  fof(f52,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f35])).
% 7.76/1.49  
% 7.76/1.49  fof(f73,plain,(
% 7.76/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f3,axiom,(
% 7.76/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f16,plain,(
% 7.76/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f3])).
% 7.76/1.49  
% 7.76/1.49  fof(f50,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f16])).
% 7.76/1.49  
% 7.76/1.49  fof(f77,plain,(
% 7.76/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f10,axiom,(
% 7.76/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f26,plain,(
% 7.76/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.76/1.49    inference(ennf_transformation,[],[f10])).
% 7.76/1.49  
% 7.76/1.49  fof(f27,plain,(
% 7.76/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.76/1.49    inference(flattening,[],[f26])).
% 7.76/1.49  
% 7.76/1.49  fof(f61,plain,(
% 7.76/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f27])).
% 7.76/1.49  
% 7.76/1.49  fof(f75,plain,(
% 7.76/1.49    v1_funct_1(sK4)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f78,plain,(
% 7.76/1.49    v1_funct_1(sK5)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f11,axiom,(
% 7.76/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f28,plain,(
% 7.76/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.76/1.49    inference(ennf_transformation,[],[f11])).
% 7.76/1.49  
% 7.76/1.49  fof(f29,plain,(
% 7.76/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.76/1.49    inference(flattening,[],[f28])).
% 7.76/1.49  
% 7.76/1.49  fof(f38,plain,(
% 7.76/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.76/1.49    inference(nnf_transformation,[],[f29])).
% 7.76/1.49  
% 7.76/1.49  fof(f39,plain,(
% 7.76/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.76/1.49    inference(flattening,[],[f38])).
% 7.76/1.49  
% 7.76/1.49  fof(f63,plain,(
% 7.76/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f39])).
% 7.76/1.49  
% 7.76/1.49  fof(f85,plain,(
% 7.76/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(equality_resolution,[],[f63])).
% 7.76/1.49  
% 7.76/1.49  fof(f12,axiom,(
% 7.76/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f30,plain,(
% 7.76/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f12])).
% 7.76/1.49  
% 7.76/1.49  fof(f31,plain,(
% 7.76/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.76/1.49    inference(flattening,[],[f30])).
% 7.76/1.49  
% 7.76/1.49  fof(f65,plain,(
% 7.76/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f31])).
% 7.76/1.49  
% 7.76/1.49  fof(f66,plain,(
% 7.76/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f31])).
% 7.76/1.49  
% 7.76/1.49  fof(f67,plain,(
% 7.76/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f31])).
% 7.76/1.49  
% 7.76/1.49  fof(f69,plain,(
% 7.76/1.49    ~v1_xboole_0(sK1)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f72,plain,(
% 7.76/1.49    ~v1_xboole_0(sK3)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f79,plain,(
% 7.76/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f70,plain,(
% 7.76/1.49    ~v1_xboole_0(sK2)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f76,plain,(
% 7.76/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f47,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f34])).
% 7.76/1.49  
% 7.76/1.49  fof(f5,axiom,(
% 7.76/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.76/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f18,plain,(
% 7.76/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f5])).
% 7.76/1.49  
% 7.76/1.49  fof(f19,plain,(
% 7.76/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.76/1.49    inference(flattening,[],[f18])).
% 7.76/1.49  
% 7.76/1.49  fof(f36,plain,(
% 7.76/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.76/1.49    inference(nnf_transformation,[],[f19])).
% 7.76/1.49  
% 7.76/1.49  fof(f53,plain,(
% 7.76/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f36])).
% 7.76/1.49  
% 7.76/1.49  fof(f74,plain,(
% 7.76/1.49    r1_subset_1(sK2,sK3)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f68,plain,(
% 7.76/1.49    ~v1_xboole_0(sK0)),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f71,plain,(
% 7.76/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f81,plain,(
% 7.76/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.76/1.49    inference(cnf_transformation,[],[f46])).
% 7.76/1.49  
% 7.76/1.49  fof(f62,plain,(
% 7.76/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f39])).
% 7.76/1.49  
% 7.76/1.49  fof(f86,plain,(
% 7.76/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(equality_resolution,[],[f62])).
% 7.76/1.49  
% 7.76/1.49  cnf(c_22,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.76/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_911,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1366,plain,
% 7.76/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_911]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.76/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_918,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.76/1.49      | v1_relat_1(X0_53) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1360,plain,
% 7.76/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.76/1.49      | v1_relat_1(X0_53) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_918]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2319,plain,
% 7.76/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1366,c_1360]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2,plain,
% 7.76/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_920,plain,
% 7.76/1.49      ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_0,plain,
% 7.76/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_250,plain,
% 7.76/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.76/1.49      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4,plain,
% 7.76/1.49      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.76/1.49      | ~ v1_relat_1(X0)
% 7.76/1.49      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_567,plain,
% 7.76/1.49      ( ~ v1_relat_1(X0)
% 7.76/1.49      | X1 != X2
% 7.76/1.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.76/1.49      | k3_xboole_0(X3,X2) != k1_xboole_0
% 7.76/1.49      | k1_relat_1(X0) != X3 ),
% 7.76/1.49      inference(resolution_lifted,[status(thm)],[c_250,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_568,plain,
% 7.76/1.49      ( ~ v1_relat_1(X0)
% 7.76/1.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.76/1.49      | k3_xboole_0(k1_relat_1(X0),X1) != k1_xboole_0 ),
% 7.76/1.49      inference(unflattening,[status(thm)],[c_567]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_896,plain,
% 7.76/1.49      ( ~ v1_relat_1(X0_53)
% 7.76/1.49      | k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.76/1.49      | k3_xboole_0(k1_relat_1(X0_53),X1_53) != k1_xboole_0 ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_568]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1381,plain,
% 7.76/1.49      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.76/1.49      | k3_xboole_0(k1_relat_1(X0_53),X1_53) != k1_xboole_0
% 7.76/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_10438,plain,
% 7.76/1.49      ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
% 7.76/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_920,c_1381]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_10499,plain,
% 7.76/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2319,c_10438]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_29,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_905,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1372,plain,
% 7.76/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_905]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.76/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_919,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.76/1.49      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1359,plain,
% 7.76/1.49      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2385,plain,
% 7.76/1.49      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1372,c_1359]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_25,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.76/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_908,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1369,plain,
% 7.76/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_908]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_14,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.76/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_917,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.76/1.49      | ~ v1_funct_1(X0_53)
% 7.76/1.49      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1361,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.76/1.49      | v1_funct_1(X2_53) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_917]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2420,plain,
% 7.76/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.76/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1369,c_1361]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_27,negated_conjecture,
% 7.76/1.49      ( v1_funct_1(sK4) ),
% 7.76/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_42,plain,
% 7.76/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2819,plain,
% 7.76/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.76/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2420,c_42]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2419,plain,
% 7.76/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.76/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1366,c_1361]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_24,negated_conjecture,
% 7.76/1.49      ( v1_funct_1(sK5) ),
% 7.76/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_45,plain,
% 7.76/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2776,plain,
% 7.76/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.76/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2419,c_45]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_16,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_20,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_19,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_18,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_195,plain,
% 7.76/1.49      ( ~ v1_funct_1(X3)
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_16,c_20,c_19,c_18]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_196,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_195]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_898,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.76/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.76/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.76/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.76/1.49      | ~ v1_funct_1(X0_53)
% 7.76/1.49      | ~ v1_funct_1(X3_53)
% 7.76/1.49      | v1_xboole_0(X2_53)
% 7.76/1.49      | v1_xboole_0(X1_53)
% 7.76/1.49      | v1_xboole_0(X4_53)
% 7.76/1.49      | v1_xboole_0(X5_53)
% 7.76/1.49      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_196]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1379,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.76/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.76/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.76/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.76/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.76/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_898]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4216,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 7.76/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.76/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.76/1.49      | v1_funct_1(sK5) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2776,c_1379]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_33,negated_conjecture,
% 7.76/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_36,plain,
% 7.76/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_30,negated_conjecture,
% 7.76/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.76/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_39,plain,
% 7.76/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_23,negated_conjecture,
% 7.76/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_46,plain,
% 7.76/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_47,plain,
% 7.76/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8034,plain,
% 7.76/1.49      ( v1_funct_1(X1_53) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.76/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 7.76/1.49      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_4216,c_36,c_39,c_45,c_46,c_47]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8035,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 7.76/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_8034]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8041,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.76/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(sK4) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2819,c_8035]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_32,negated_conjecture,
% 7.76/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.76/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_37,plain,
% 7.76/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_26,negated_conjecture,
% 7.76/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_43,plain,
% 7.76/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_44,plain,
% 7.76/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8067,plain,
% 7.76/1.49      ( v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_8041,c_37,c_42,c_43,c_44]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8068,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_8067]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8073,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2385,c_8068]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1,plain,
% 7.76/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_252,plain,
% 7.76/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.76/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7,plain,
% 7.76/1.49      ( ~ r1_subset_1(X0,X1)
% 7.76/1.49      | r1_xboole_0(X0,X1)
% 7.76/1.49      | v1_xboole_0(X0)
% 7.76/1.49      | v1_xboole_0(X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_28,negated_conjecture,
% 7.76/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.76/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_520,plain,
% 7.76/1.49      ( r1_xboole_0(X0,X1)
% 7.76/1.49      | v1_xboole_0(X0)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | sK3 != X1
% 7.76/1.49      | sK2 != X0 ),
% 7.76/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_521,plain,
% 7.76/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.76/1.49      inference(unflattening,[status(thm)],[c_520]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_523,plain,
% 7.76/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_521,c_32,c_30]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_597,plain,
% 7.76/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 7.76/1.49      inference(resolution_lifted,[status(thm)],[c_252,c_523]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_598,plain,
% 7.76/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.76/1.49      inference(unflattening,[status(thm)],[c_597]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_894,plain,
% 7.76/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_598]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8074,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_8073,c_894]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_913,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.76/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.76/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.76/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.76/1.49      | ~ v1_funct_1(X0_53)
% 7.76/1.49      | ~ v1_funct_1(X3_53)
% 7.76/1.49      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 7.76/1.49      | v1_xboole_0(X2_53)
% 7.76/1.49      | v1_xboole_0(X1_53)
% 7.76/1.49      | v1_xboole_0(X4_53)
% 7.76/1.49      | v1_xboole_0(X5_53) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1365,plain,
% 7.76/1.49      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.76/1.49      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.76/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.76/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.76/1.49      | v1_funct_1(X3_53) != iProver_top
% 7.76/1.49      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.76/1.49      | v1_xboole_0(X5_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_913]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_915,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.76/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.76/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.76/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.76/1.49      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 7.76/1.49      | ~ v1_funct_1(X0_53)
% 7.76/1.49      | ~ v1_funct_1(X3_53)
% 7.76/1.49      | v1_xboole_0(X2_53)
% 7.76/1.49      | v1_xboole_0(X1_53)
% 7.76/1.49      | v1_xboole_0(X4_53)
% 7.76/1.49      | v1_xboole_0(X5_53) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1363,plain,
% 7.76/1.49      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.76/1.49      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.76/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.76/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.76/1.49      | v1_funct_1(X3_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X5_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_915]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2561,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.76/1.49      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.76/1.49      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.76/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.76/1.49      | v1_funct_1(X4_53) != iProver_top
% 7.76/1.49      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1363,c_1361]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4369,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.76/1.49      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.76/1.49      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.76/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.76/1.49      | v1_funct_1(X4_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1365,c_2561]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4374,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.76/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.76/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.76/1.49      | v1_funct_1(sK5) != iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1366,c_4369]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4429,plain,
% 7.76/1.49      ( v1_funct_1(X2_53) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.76/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_4374,c_36,c_39,c_45,c_46]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4430,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.76/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_4429]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4436,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.76/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(sK4) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1369,c_4430]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4530,plain,
% 7.76/1.49      ( v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_4436,c_37,c_42,c_43]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4531,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_4530]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4536,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1372,c_4531]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_34,negated_conjecture,
% 7.76/1.49      ( ~ v1_xboole_0(sK0) ),
% 7.76/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_35,plain,
% 7.76/1.49      ( v1_xboole_0(sK0) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_31,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_38,plain,
% 7.76/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4546,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_4536,c_35,c_38]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8075,plain,
% 7.76/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_8074,c_2385,c_4546]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8076,plain,
% 7.76/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_8075,c_894]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_21,negated_conjecture,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_912,negated_conjecture,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2416,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_2385,c_912]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2417,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_2416,c_894]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2822,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_2417,c_2776,c_2819]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4549,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_4546,c_2822]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4550,plain,
% 7.76/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.76/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_4549,c_4546]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_17,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.76/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_188,plain,
% 7.76/1.49      ( ~ v1_funct_1(X3)
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_17,c_20,c_19,c_18]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_189,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.76/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.76/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.76/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.76/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.76/1.49      | ~ v1_funct_1(X0)
% 7.76/1.49      | ~ v1_funct_1(X3)
% 7.76/1.49      | v1_xboole_0(X1)
% 7.76/1.49      | v1_xboole_0(X2)
% 7.76/1.49      | v1_xboole_0(X4)
% 7.76/1.49      | v1_xboole_0(X5)
% 7.76/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_188]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_899,plain,
% 7.76/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.76/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.76/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.76/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.76/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.76/1.49      | ~ v1_funct_1(X0_53)
% 7.76/1.49      | ~ v1_funct_1(X3_53)
% 7.76/1.49      | v1_xboole_0(X2_53)
% 7.76/1.49      | v1_xboole_0(X1_53)
% 7.76/1.49      | v1_xboole_0(X4_53)
% 7.76/1.49      | v1_xboole_0(X5_53)
% 7.76/1.49      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.76/1.49      inference(subtyping,[status(esa)],[c_189]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1378,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.76/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.76/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.76/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.76/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.76/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.76/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3811,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.76/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.76/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.76/1.49      | v1_funct_1(sK5) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2776,c_1378]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4985,plain,
% 7.76/1.49      ( v1_funct_1(X1_53) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.76/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.76/1.49      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_3811,c_36,c_39,c_45,c_46,c_47]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4986,plain,
% 7.76/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.76/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.76/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.76/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_4985]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4992,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.76/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.76/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_funct_1(sK4) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2819,c_4986]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5106,plain,
% 7.76/1.49      ( v1_xboole_0(X0_53) = iProver_top
% 7.76/1.49      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_4992,c_37,c_42,c_43,c_44]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5107,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.76/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_5106]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5112,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2385,c_5107]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5113,plain,
% 7.76/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_5112,c_894]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5114,plain,
% 7.76/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_5113,c_2385,c_4546]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5115,plain,
% 7.76/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 7.76/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.76/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_5114,c_894]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5116,plain,
% 7.76/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.76/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.76/1.49      | v1_xboole_0(sK0)
% 7.76/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5115]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5221,plain,
% 7.76/1.49      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 7.76/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_5115,c_34,c_31,c_29,c_5116]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5222,plain,
% 7.76/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(renaming,[status(thm)],[c_5221]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8077,plain,
% 7.76/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.76/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.76/1.49      | v1_xboole_0(sK0)
% 7.76/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.76/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_8076]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_8095,plain,
% 7.76/1.49      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_8076,c_34,c_31,c_29,c_4550,c_5222,c_8077]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_10506,plain,
% 7.76/1.49      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_10499,c_8095]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2320,plain,
% 7.76/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1369,c_1360]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_10500,plain,
% 7.76/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_2320,c_10438]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_10508,plain,
% 7.76/1.49      ( k1_xboole_0 != k1_xboole_0 ),
% 7.76/1.49      inference(light_normalisation,[status(thm)],[c_10506,c_10500]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_10509,plain,
% 7.76/1.49      ( $false ),
% 7.76/1.49      inference(equality_resolution_simp,[status(thm)],[c_10508]) ).
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  ------                               Statistics
% 7.76/1.49  
% 7.76/1.49  ------ General
% 7.76/1.49  
% 7.76/1.49  abstr_ref_over_cycles:                  0
% 7.76/1.49  abstr_ref_under_cycles:                 0
% 7.76/1.49  gc_basic_clause_elim:                   0
% 7.76/1.49  forced_gc_time:                         0
% 7.76/1.49  parsing_time:                           0.01
% 7.76/1.49  unif_index_cands_time:                  0.
% 7.76/1.49  unif_index_add_time:                    0.
% 7.76/1.49  orderings_time:                         0.
% 7.76/1.49  out_proof_time:                         0.018
% 7.76/1.49  total_time:                             0.732
% 7.76/1.49  num_of_symbols:                         58
% 7.76/1.49  num_of_terms:                           31316
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing
% 7.76/1.49  
% 7.76/1.49  num_of_splits:                          0
% 7.76/1.49  num_of_split_atoms:                     0
% 7.76/1.49  num_of_reused_defs:                     0
% 7.76/1.49  num_eq_ax_congr_red:                    14
% 7.76/1.49  num_of_sem_filtered_clauses:            1
% 7.76/1.49  num_of_subtypes:                        2
% 7.76/1.49  monotx_restored_types:                  0
% 7.76/1.49  sat_num_of_epr_types:                   0
% 7.76/1.49  sat_num_of_non_cyclic_types:            0
% 7.76/1.49  sat_guarded_non_collapsed_types:        1
% 7.76/1.49  num_pure_diseq_elim:                    0
% 7.76/1.49  simp_replaced_by:                       0
% 7.76/1.49  res_preprocessed:                       149
% 7.76/1.49  prep_upred:                             0
% 7.76/1.49  prep_unflattend:                        13
% 7.76/1.49  smt_new_axioms:                         0
% 7.76/1.49  pred_elim_cands:                        5
% 7.76/1.49  pred_elim:                              4
% 7.76/1.49  pred_elim_cl:                           6
% 7.76/1.49  pred_elim_cycles:                       7
% 7.76/1.49  merged_defs:                            2
% 7.76/1.49  merged_defs_ncl:                        0
% 7.76/1.49  bin_hyper_res:                          2
% 7.76/1.49  prep_cycles:                            4
% 7.76/1.49  pred_elim_time:                         0.006
% 7.76/1.49  splitting_time:                         0.
% 7.76/1.49  sem_filter_time:                        0.
% 7.76/1.49  monotx_time:                            0.
% 7.76/1.49  subtype_inf_time:                       0.001
% 7.76/1.49  
% 7.76/1.49  ------ Problem properties
% 7.76/1.49  
% 7.76/1.49  clauses:                                28
% 7.76/1.49  conjectures:                            13
% 7.76/1.49  epr:                                    8
% 7.76/1.49  horn:                                   21
% 7.76/1.49  ground:                                 14
% 7.76/1.49  unary:                                  14
% 7.76/1.49  binary:                                 2
% 7.76/1.49  lits:                                   122
% 7.76/1.49  lits_eq:                                20
% 7.76/1.49  fd_pure:                                0
% 7.76/1.49  fd_pseudo:                              0
% 7.76/1.49  fd_cond:                                0
% 7.76/1.49  fd_pseudo_cond:                         1
% 7.76/1.49  ac_symbols:                             0
% 7.76/1.49  
% 7.76/1.49  ------ Propositional Solver
% 7.76/1.49  
% 7.76/1.49  prop_solver_calls:                      29
% 7.76/1.49  prop_fast_solver_calls:                 3924
% 7.76/1.49  smt_solver_calls:                       0
% 7.76/1.49  smt_fast_solver_calls:                  0
% 7.76/1.49  prop_num_of_clauses:                    6078
% 7.76/1.49  prop_preprocess_simplified:             11065
% 7.76/1.49  prop_fo_subsumed:                       303
% 7.76/1.49  prop_solver_time:                       0.
% 7.76/1.49  smt_solver_time:                        0.
% 7.76/1.49  smt_fast_solver_time:                   0.
% 7.76/1.49  prop_fast_solver_time:                  0.
% 7.76/1.49  prop_unsat_core_time:                   0.
% 7.76/1.49  
% 7.76/1.49  ------ QBF
% 7.76/1.49  
% 7.76/1.49  qbf_q_res:                              0
% 7.76/1.49  qbf_num_tautologies:                    0
% 7.76/1.49  qbf_prep_cycles:                        0
% 7.76/1.49  
% 7.76/1.49  ------ BMC1
% 7.76/1.49  
% 7.76/1.49  bmc1_current_bound:                     -1
% 7.76/1.49  bmc1_last_solved_bound:                 -1
% 7.76/1.49  bmc1_unsat_core_size:                   -1
% 7.76/1.49  bmc1_unsat_core_parents_size:           -1
% 7.76/1.49  bmc1_merge_next_fun:                    0
% 7.76/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation
% 7.76/1.49  
% 7.76/1.49  inst_num_of_clauses:                    1293
% 7.76/1.49  inst_num_in_passive:                    285
% 7.76/1.49  inst_num_in_active:                     786
% 7.76/1.49  inst_num_in_unprocessed:                222
% 7.76/1.49  inst_num_of_loops:                      910
% 7.76/1.49  inst_num_of_learning_restarts:          0
% 7.76/1.49  inst_num_moves_active_passive:          121
% 7.76/1.49  inst_lit_activity:                      0
% 7.76/1.49  inst_lit_activity_moves:                1
% 7.76/1.49  inst_num_tautologies:                   0
% 7.76/1.49  inst_num_prop_implied:                  0
% 7.76/1.49  inst_num_existing_simplified:           0
% 7.76/1.49  inst_num_eq_res_simplified:             0
% 7.76/1.49  inst_num_child_elim:                    0
% 7.76/1.49  inst_num_of_dismatching_blockings:      97
% 7.76/1.49  inst_num_of_non_proper_insts:           1335
% 7.76/1.49  inst_num_of_duplicates:                 0
% 7.76/1.49  inst_inst_num_from_inst_to_res:         0
% 7.76/1.49  inst_dismatching_checking_time:         0.
% 7.76/1.49  
% 7.76/1.49  ------ Resolution
% 7.76/1.49  
% 7.76/1.49  res_num_of_clauses:                     0
% 7.76/1.49  res_num_in_passive:                     0
% 7.76/1.49  res_num_in_active:                      0
% 7.76/1.49  res_num_of_loops:                       153
% 7.76/1.49  res_forward_subset_subsumed:            14
% 7.76/1.49  res_backward_subset_subsumed:           0
% 7.76/1.49  res_forward_subsumed:                   0
% 7.76/1.49  res_backward_subsumed:                  0
% 7.76/1.49  res_forward_subsumption_resolution:     1
% 7.76/1.49  res_backward_subsumption_resolution:    0
% 7.76/1.49  res_clause_to_clause_subsumption:       927
% 7.76/1.49  res_orphan_elimination:                 0
% 7.76/1.49  res_tautology_del:                      14
% 7.76/1.49  res_num_eq_res_simplified:              0
% 7.76/1.49  res_num_sel_changes:                    0
% 7.76/1.49  res_moves_from_active_to_pass:          0
% 7.76/1.49  
% 7.76/1.49  ------ Superposition
% 7.76/1.49  
% 7.76/1.49  sup_time_total:                         0.
% 7.76/1.49  sup_time_generating:                    0.
% 7.76/1.49  sup_time_sim_full:                      0.
% 7.76/1.49  sup_time_sim_immed:                     0.
% 7.76/1.49  
% 7.76/1.49  sup_num_of_clauses:                     287
% 7.76/1.49  sup_num_in_active:                      151
% 7.76/1.49  sup_num_in_passive:                     136
% 7.76/1.49  sup_num_of_loops:                       181
% 7.76/1.49  sup_fw_superposition:                   299
% 7.76/1.49  sup_bw_superposition:                   51
% 7.76/1.49  sup_immediate_simplified:               153
% 7.76/1.49  sup_given_eliminated:                   0
% 7.76/1.49  comparisons_done:                       0
% 7.76/1.49  comparisons_avoided:                    0
% 7.76/1.49  
% 7.76/1.49  ------ Simplifications
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  sim_fw_subset_subsumed:                 2
% 7.76/1.49  sim_bw_subset_subsumed:                 0
% 7.76/1.49  sim_fw_subsumed:                        31
% 7.76/1.49  sim_bw_subsumed:                        33
% 7.76/1.49  sim_fw_subsumption_res:                 0
% 7.76/1.49  sim_bw_subsumption_res:                 0
% 7.76/1.49  sim_tautology_del:                      0
% 7.76/1.49  sim_eq_tautology_del:                   5
% 7.76/1.49  sim_eq_res_simp:                        0
% 7.76/1.49  sim_fw_demodulated:                     85
% 7.76/1.49  sim_bw_demodulated:                     5
% 7.76/1.49  sim_light_normalised:                   51
% 7.76/1.49  sim_joinable_taut:                      0
% 7.76/1.49  sim_joinable_simp:                      0
% 7.76/1.49  sim_ac_normalised:                      0
% 7.76/1.49  sim_smt_subsumption:                    0
% 7.76/1.49  
%------------------------------------------------------------------------------
