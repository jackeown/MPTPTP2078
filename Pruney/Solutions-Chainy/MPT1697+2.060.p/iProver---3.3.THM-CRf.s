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
% DateTime   : Thu Dec  3 12:21:35 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :  225 (3088 expanded)
%              Number of clauses        :  156 ( 815 expanded)
%              Number of leaves         :   17 (1197 expanded)
%              Depth                    :   22
%              Number of atoms          : 1296 (40096 expanded)
%              Number of equality atoms :  605 (9577 expanded)
%              Maximal formula depth    :   25 (   6 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f33])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f45,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f44,f43,f42,f41,f40,f39])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f74,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f45])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f29])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f30])).

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
    inference(flattening,[],[f37])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
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
    inference(equality_resolution,[],[f58])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f31])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f77,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_372,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1145,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1137,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_2455,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1137])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1858,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_6610,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2455,c_24,c_22,c_1858])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_368,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1149,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1129,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_1886,plain,
    ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1149,c_1129])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_375,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1142,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_2454,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1137])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1853,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_6204,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2454,c_21,c_19,c_1853])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_329,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_17,c_16,c_15])).

cnf(c_330,plain,
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
    inference(renaming,[status(thm)],[c_329])).

cnf(c_362,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51)
    | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
    | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_1155,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
    | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_6209,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_1155])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_29741,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6209,c_33,c_36,c_42,c_43,c_44])).

cnf(c_29742,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_29741])).

cnf(c_29762,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_29742])).

cnf(c_29852,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29762,c_1886])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_51622,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29852,c_32,c_37])).

cnf(c_51623,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_51622])).

cnf(c_51636,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6610,c_51623])).

cnf(c_25,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_369,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1148,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_384,plain,
    ( ~ r1_subset_1(X0_51,X1_51)
    | r1_xboole_0(X0_51,X1_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1134,plain,
    ( r1_subset_1(X0_51,X1_51) != iProver_top
    | r1_xboole_0(X0_51,X1_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_2230,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1134])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1553,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_1554,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1553])).

cnf(c_5332,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2230,c_34,c_36,c_38,c_1554])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_391,plain,
    ( ~ r1_xboole_0(X0_51,X1_51)
    | k3_xboole_0(X0_51,X1_51) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1127,plain,
    ( k3_xboole_0(X0_51,X1_51) = k1_xboole_0
    | r1_xboole_0(X0_51,X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_5337,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5332,c_1127])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1135,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_2150,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1135])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_388,plain,
    ( ~ v1_relat_1(X0_51)
    | k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1130,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51))
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_3220,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_51,X1_51)) = k7_relat_1(k7_relat_1(sK5,X0_51),X1_51) ),
    inference(superposition,[status(thm)],[c_2150,c_1130])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_387,plain,
    ( ~ r1_xboole_0(X0_51,X1_51)
    | ~ v1_relat_1(X2_51)
    | k7_relat_1(k7_relat_1(X2_51,X0_51),X1_51) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1131,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
    | r1_xboole_0(X1_51,X2_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_5339,plain,
    ( k7_relat_1(k7_relat_1(X0_51,sK2),sK3) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_5332,c_1131])).

cnf(c_5820,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2150,c_5339])).

cnf(c_23649,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3220,c_5820])).

cnf(c_23651,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23649,c_5337])).

cnf(c_51720,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51636,c_5337,c_23651])).

cnf(c_379,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1139,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_xboole_0(X5_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_2830,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
    | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_1139,c_1137])).

cnf(c_377,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1141,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
    | v1_xboole_0(X5_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_7814,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
    | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2830,c_1141])).

cnf(c_7818,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_7814])).

cnf(c_8979,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7818,c_33,c_36,c_42,c_43])).

cnf(c_8980,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_8979])).

cnf(c_8994,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_8980])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9459,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8994,c_34,c_39,c_40])).

cnf(c_9460,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_9459])).

cnf(c_9469,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_9460])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_9600,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9469,c_32,c_35])).

cnf(c_51721,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_51720,c_9600])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f80])).

cnf(c_338,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_17,c_16,c_15])).

cnf(c_339,plain,
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
    inference(renaming,[status(thm)],[c_338])).

cnf(c_361,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51)
    | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
    | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_1156,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
    | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_361])).

cnf(c_6208,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_1156])).

cnf(c_28833,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6208,c_33,c_36,c_42,c_43,c_44])).

cnf(c_28834,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_28833])).

cnf(c_28854,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_28834])).

cnf(c_28944,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28854,c_1886])).

cnf(c_3623,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(sK0,X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1156])).

cnf(c_3739,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k3_xboole_0(X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3623,c_1886])).

cnf(c_13276,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
    | k2_partfun1(X0_51,X1_51,X2_51,k3_xboole_0(X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3739,c_32,c_36,c_37])).

cnf(c_13277,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k3_xboole_0(X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_13276])).

cnf(c_13299,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6204,c_13277])).

cnf(c_51250,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28944,c_32,c_37])).

cnf(c_51251,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_51250])).

cnf(c_51264,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6610,c_51251])).

cnf(c_51348,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_51264,c_5337,c_23651])).

cnf(c_51349,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_51348,c_9600])).

cnf(c_18,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_376,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3621,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1886,c_376])).

cnf(c_5815,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5337,c_3621])).

cnf(c_6742,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5815,c_6204,c_6610])).

cnf(c_9604,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9600,c_6742])).

cnf(c_9605,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_9604,c_9600])).

cnf(c_43509,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9605,c_23651])).

cnf(c_2151,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1135])).

cnf(c_3336,plain,
    ( k7_relat_1(sK4,k3_xboole_0(X0_51,X1_51)) = k7_relat_1(k7_relat_1(sK4,X0_51),X1_51) ),
    inference(superposition,[status(thm)],[c_2151,c_1130])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X0_51,X2_51) = k9_subset_1(X1_51,X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1128,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k9_subset_1(X0_51,X2_51,X1_51)
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_390])).

cnf(c_1887,plain,
    ( k9_subset_1(sK0,sK3,X0_51) = k9_subset_1(sK0,X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1149,c_1128])).

cnf(c_1891,plain,
    ( k9_subset_1(sK0,sK3,X0_51) = k3_xboole_0(X0_51,sK3) ),
    inference(demodulation,[status(thm)],[c_1886,c_1887])).

cnf(c_366,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1899,plain,
    ( k9_subset_1(sK0,X0_51,sK2) = k3_xboole_0(X0_51,sK2) ),
    inference(superposition,[status(thm)],[c_1151,c_1129])).

cnf(c_4493,plain,
    ( k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1891,c_1899])).

cnf(c_17769,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4493,c_5337])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_392,plain,
    ( r1_xboole_0(X0_51,X1_51)
    | k3_xboole_0(X0_51,X1_51) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1126,plain,
    ( k3_xboole_0(X0_51,X1_51) != k1_xboole_0
    | r1_xboole_0(X0_51,X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_17771,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17769,c_1126])).

cnf(c_17870,plain,
    ( k7_relat_1(k7_relat_1(X0_51,sK3),sK2) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_17771,c_1131])).

cnf(c_18012,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK3),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2151,c_17870])).

cnf(c_24057,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3336,c_18012])).

cnf(c_24059,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_24057,c_17769])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_51721,c_51349,c_43509,c_24059,c_41,c_40,c_39,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:24:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.77/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.77/2.99  
% 19.77/2.99  ------  iProver source info
% 19.77/2.99  
% 19.77/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.77/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.77/2.99  git: non_committed_changes: false
% 19.77/2.99  git: last_make_outside_of_git: false
% 19.77/2.99  
% 19.77/2.99  ------ 
% 19.77/2.99  
% 19.77/2.99  ------ Input Options
% 19.77/2.99  
% 19.77/2.99  --out_options                           all
% 19.77/2.99  --tptp_safe_out                         true
% 19.77/2.99  --problem_path                          ""
% 19.77/2.99  --include_path                          ""
% 19.77/2.99  --clausifier                            res/vclausify_rel
% 19.77/2.99  --clausifier_options                    --mode clausify
% 19.77/2.99  --stdin                                 false
% 19.77/2.99  --stats_out                             sel
% 19.77/2.99  
% 19.77/2.99  ------ General Options
% 19.77/2.99  
% 19.77/2.99  --fof                                   false
% 19.77/2.99  --time_out_real                         604.99
% 19.77/2.99  --time_out_virtual                      -1.
% 19.77/2.99  --symbol_type_check                     false
% 19.77/2.99  --clausify_out                          false
% 19.77/2.99  --sig_cnt_out                           false
% 19.77/2.99  --trig_cnt_out                          false
% 19.77/2.99  --trig_cnt_out_tolerance                1.
% 19.77/2.99  --trig_cnt_out_sk_spl                   false
% 19.77/2.99  --abstr_cl_out                          false
% 19.77/2.99  
% 19.77/2.99  ------ Global Options
% 19.77/2.99  
% 19.77/2.99  --schedule                              none
% 19.77/2.99  --add_important_lit                     false
% 19.77/2.99  --prop_solver_per_cl                    1000
% 19.77/2.99  --min_unsat_core                        false
% 19.77/2.99  --soft_assumptions                      false
% 19.77/2.99  --soft_lemma_size                       3
% 19.77/2.99  --prop_impl_unit_size                   0
% 19.77/2.99  --prop_impl_unit                        []
% 19.77/2.99  --share_sel_clauses                     true
% 19.77/2.99  --reset_solvers                         false
% 19.77/2.99  --bc_imp_inh                            [conj_cone]
% 19.77/2.99  --conj_cone_tolerance                   3.
% 19.77/2.99  --extra_neg_conj                        none
% 19.77/2.99  --large_theory_mode                     true
% 19.77/2.99  --prolific_symb_bound                   200
% 19.77/2.99  --lt_threshold                          2000
% 19.77/2.99  --clause_weak_htbl                      true
% 19.77/2.99  --gc_record_bc_elim                     false
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing Options
% 19.77/2.99  
% 19.77/2.99  --preprocessing_flag                    true
% 19.77/2.99  --time_out_prep_mult                    0.1
% 19.77/2.99  --splitting_mode                        input
% 19.77/2.99  --splitting_grd                         true
% 19.77/2.99  --splitting_cvd                         false
% 19.77/2.99  --splitting_cvd_svl                     false
% 19.77/2.99  --splitting_nvd                         32
% 19.77/2.99  --sub_typing                            true
% 19.77/2.99  --prep_gs_sim                           false
% 19.77/2.99  --prep_unflatten                        true
% 19.77/2.99  --prep_res_sim                          true
% 19.77/2.99  --prep_upred                            true
% 19.77/2.99  --prep_sem_filter                       exhaustive
% 19.77/2.99  --prep_sem_filter_out                   false
% 19.77/2.99  --pred_elim                             false
% 19.77/2.99  --res_sim_input                         true
% 19.77/2.99  --eq_ax_congr_red                       true
% 19.77/2.99  --pure_diseq_elim                       true
% 19.77/2.99  --brand_transform                       false
% 19.77/2.99  --non_eq_to_eq                          false
% 19.77/2.99  --prep_def_merge                        true
% 19.77/2.99  --prep_def_merge_prop_impl              false
% 19.77/2.99  --prep_def_merge_mbd                    true
% 19.77/2.99  --prep_def_merge_tr_red                 false
% 19.77/2.99  --prep_def_merge_tr_cl                  false
% 19.77/2.99  --smt_preprocessing                     true
% 19.77/2.99  --smt_ac_axioms                         fast
% 19.77/2.99  --preprocessed_out                      false
% 19.77/2.99  --preprocessed_stats                    false
% 19.77/2.99  
% 19.77/2.99  ------ Abstraction refinement Options
% 19.77/2.99  
% 19.77/2.99  --abstr_ref                             []
% 19.77/2.99  --abstr_ref_prep                        false
% 19.77/2.99  --abstr_ref_until_sat                   false
% 19.77/2.99  --abstr_ref_sig_restrict                funpre
% 19.77/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/2.99  --abstr_ref_under                       []
% 19.77/2.99  
% 19.77/2.99  ------ SAT Options
% 19.77/2.99  
% 19.77/2.99  --sat_mode                              false
% 19.77/2.99  --sat_fm_restart_options                ""
% 19.77/2.99  --sat_gr_def                            false
% 19.77/2.99  --sat_epr_types                         true
% 19.77/2.99  --sat_non_cyclic_types                  false
% 19.77/2.99  --sat_finite_models                     false
% 19.77/2.99  --sat_fm_lemmas                         false
% 19.77/2.99  --sat_fm_prep                           false
% 19.77/2.99  --sat_fm_uc_incr                        true
% 19.77/2.99  --sat_out_model                         small
% 19.77/2.99  --sat_out_clauses                       false
% 19.77/2.99  
% 19.77/2.99  ------ QBF Options
% 19.77/2.99  
% 19.77/2.99  --qbf_mode                              false
% 19.77/2.99  --qbf_elim_univ                         false
% 19.77/2.99  --qbf_dom_inst                          none
% 19.77/2.99  --qbf_dom_pre_inst                      false
% 19.77/2.99  --qbf_sk_in                             false
% 19.77/2.99  --qbf_pred_elim                         true
% 19.77/2.99  --qbf_split                             512
% 19.77/2.99  
% 19.77/2.99  ------ BMC1 Options
% 19.77/2.99  
% 19.77/2.99  --bmc1_incremental                      false
% 19.77/2.99  --bmc1_axioms                           reachable_all
% 19.77/2.99  --bmc1_min_bound                        0
% 19.77/2.99  --bmc1_max_bound                        -1
% 19.77/2.99  --bmc1_max_bound_default                -1
% 19.77/2.99  --bmc1_symbol_reachability              true
% 19.77/2.99  --bmc1_property_lemmas                  false
% 19.77/2.99  --bmc1_k_induction                      false
% 19.77/2.99  --bmc1_non_equiv_states                 false
% 19.77/2.99  --bmc1_deadlock                         false
% 19.77/2.99  --bmc1_ucm                              false
% 19.77/2.99  --bmc1_add_unsat_core                   none
% 19.77/2.99  --bmc1_unsat_core_children              false
% 19.77/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/2.99  --bmc1_out_stat                         full
% 19.77/2.99  --bmc1_ground_init                      false
% 19.77/2.99  --bmc1_pre_inst_next_state              false
% 19.77/2.99  --bmc1_pre_inst_state                   false
% 19.77/2.99  --bmc1_pre_inst_reach_state             false
% 19.77/2.99  --bmc1_out_unsat_core                   false
% 19.77/2.99  --bmc1_aig_witness_out                  false
% 19.77/2.99  --bmc1_verbose                          false
% 19.77/2.99  --bmc1_dump_clauses_tptp                false
% 19.77/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.77/2.99  --bmc1_dump_file                        -
% 19.77/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.77/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.77/2.99  --bmc1_ucm_extend_mode                  1
% 19.77/2.99  --bmc1_ucm_init_mode                    2
% 19.77/2.99  --bmc1_ucm_cone_mode                    none
% 19.77/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.77/2.99  --bmc1_ucm_relax_model                  4
% 19.77/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.77/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/2.99  --bmc1_ucm_layered_model                none
% 19.77/2.99  --bmc1_ucm_max_lemma_size               10
% 19.77/2.99  
% 19.77/2.99  ------ AIG Options
% 19.77/2.99  
% 19.77/2.99  --aig_mode                              false
% 19.77/2.99  
% 19.77/2.99  ------ Instantiation Options
% 19.77/2.99  
% 19.77/2.99  --instantiation_flag                    true
% 19.77/2.99  --inst_sos_flag                         false
% 19.77/2.99  --inst_sos_phase                        true
% 19.77/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel_side                     num_symb
% 19.77/2.99  --inst_solver_per_active                1400
% 19.77/2.99  --inst_solver_calls_frac                1.
% 19.77/2.99  --inst_passive_queue_type               priority_queues
% 19.77/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/2.99  --inst_passive_queues_freq              [25;2]
% 19.77/2.99  --inst_dismatching                      true
% 19.77/2.99  --inst_eager_unprocessed_to_passive     true
% 19.77/2.99  --inst_prop_sim_given                   true
% 19.77/2.99  --inst_prop_sim_new                     false
% 19.77/2.99  --inst_subs_new                         false
% 19.77/2.99  --inst_eq_res_simp                      false
% 19.77/2.99  --inst_subs_given                       false
% 19.77/2.99  --inst_orphan_elimination               true
% 19.77/2.99  --inst_learning_loop_flag               true
% 19.77/2.99  --inst_learning_start                   3000
% 19.77/2.99  --inst_learning_factor                  2
% 19.77/2.99  --inst_start_prop_sim_after_learn       3
% 19.77/2.99  --inst_sel_renew                        solver
% 19.77/2.99  --inst_lit_activity_flag                true
% 19.77/2.99  --inst_restr_to_given                   false
% 19.77/2.99  --inst_activity_threshold               500
% 19.77/2.99  --inst_out_proof                        true
% 19.77/2.99  
% 19.77/2.99  ------ Resolution Options
% 19.77/2.99  
% 19.77/2.99  --resolution_flag                       true
% 19.77/2.99  --res_lit_sel                           adaptive
% 19.77/2.99  --res_lit_sel_side                      none
% 19.77/2.99  --res_ordering                          kbo
% 19.77/2.99  --res_to_prop_solver                    active
% 19.77/2.99  --res_prop_simpl_new                    false
% 19.77/2.99  --res_prop_simpl_given                  true
% 19.77/2.99  --res_passive_queue_type                priority_queues
% 19.77/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/2.99  --res_passive_queues_freq               [15;5]
% 19.77/2.99  --res_forward_subs                      full
% 19.77/2.99  --res_backward_subs                     full
% 19.77/2.99  --res_forward_subs_resolution           true
% 19.77/2.99  --res_backward_subs_resolution          true
% 19.77/2.99  --res_orphan_elimination                true
% 19.77/2.99  --res_time_limit                        2.
% 19.77/2.99  --res_out_proof                         true
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Options
% 19.77/2.99  
% 19.77/2.99  --superposition_flag                    true
% 19.77/2.99  --sup_passive_queue_type                priority_queues
% 19.77/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/2.99  --sup_passive_queues_freq               [1;4]
% 19.77/2.99  --demod_completeness_check              fast
% 19.77/2.99  --demod_use_ground                      true
% 19.77/2.99  --sup_to_prop_solver                    passive
% 19.77/2.99  --sup_prop_simpl_new                    true
% 19.77/2.99  --sup_prop_simpl_given                  true
% 19.77/2.99  --sup_fun_splitting                     false
% 19.77/2.99  --sup_smt_interval                      50000
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Simplification Setup
% 19.77/2.99  
% 19.77/2.99  --sup_indices_passive                   []
% 19.77/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_full_bw                           [BwDemod]
% 19.77/2.99  --sup_immed_triv                        [TrivRules]
% 19.77/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_immed_bw_main                     []
% 19.77/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  
% 19.77/2.99  ------ Combination Options
% 19.77/2.99  
% 19.77/2.99  --comb_res_mult                         3
% 19.77/2.99  --comb_sup_mult                         2
% 19.77/2.99  --comb_inst_mult                        10
% 19.77/2.99  
% 19.77/2.99  ------ Debug Options
% 19.77/2.99  
% 19.77/2.99  --dbg_backtrace                         false
% 19.77/2.99  --dbg_dump_prop_clauses                 false
% 19.77/2.99  --dbg_dump_prop_clauses_file            -
% 19.77/2.99  --dbg_out_stat                          false
% 19.77/2.99  ------ Parsing...
% 19.77/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.77/2.99  ------ Proving...
% 19.77/2.99  ------ Problem Properties 
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  clauses                                 32
% 19.77/2.99  conjectures                             14
% 19.77/2.99  EPR                                     11
% 19.77/2.99  Horn                                    24
% 19.77/2.99  unary                                   13
% 19.77/2.99  binary                                  7
% 19.77/2.99  lits                                    131
% 19.77/2.99  lits eq                                 17
% 19.77/2.99  fd_pure                                 0
% 19.77/2.99  fd_pseudo                               0
% 19.77/2.99  fd_cond                                 0
% 19.77/2.99  fd_pseudo_cond                          0
% 19.77/2.99  AC symbols                              0
% 19.77/2.99  
% 19.77/2.99  ------ Input Options Time Limit: Unbounded
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  ------ 
% 19.77/2.99  Current options:
% 19.77/2.99  ------ 
% 19.77/2.99  
% 19.77/2.99  ------ Input Options
% 19.77/2.99  
% 19.77/2.99  --out_options                           all
% 19.77/2.99  --tptp_safe_out                         true
% 19.77/2.99  --problem_path                          ""
% 19.77/2.99  --include_path                          ""
% 19.77/2.99  --clausifier                            res/vclausify_rel
% 19.77/2.99  --clausifier_options                    --mode clausify
% 19.77/2.99  --stdin                                 false
% 19.77/2.99  --stats_out                             sel
% 19.77/2.99  
% 19.77/2.99  ------ General Options
% 19.77/2.99  
% 19.77/2.99  --fof                                   false
% 19.77/2.99  --time_out_real                         604.99
% 19.77/2.99  --time_out_virtual                      -1.
% 19.77/2.99  --symbol_type_check                     false
% 19.77/2.99  --clausify_out                          false
% 19.77/2.99  --sig_cnt_out                           false
% 19.77/2.99  --trig_cnt_out                          false
% 19.77/2.99  --trig_cnt_out_tolerance                1.
% 19.77/2.99  --trig_cnt_out_sk_spl                   false
% 19.77/2.99  --abstr_cl_out                          false
% 19.77/2.99  
% 19.77/2.99  ------ Global Options
% 19.77/2.99  
% 19.77/2.99  --schedule                              none
% 19.77/2.99  --add_important_lit                     false
% 19.77/2.99  --prop_solver_per_cl                    1000
% 19.77/2.99  --min_unsat_core                        false
% 19.77/2.99  --soft_assumptions                      false
% 19.77/2.99  --soft_lemma_size                       3
% 19.77/2.99  --prop_impl_unit_size                   0
% 19.77/2.99  --prop_impl_unit                        []
% 19.77/2.99  --share_sel_clauses                     true
% 19.77/2.99  --reset_solvers                         false
% 19.77/2.99  --bc_imp_inh                            [conj_cone]
% 19.77/2.99  --conj_cone_tolerance                   3.
% 19.77/2.99  --extra_neg_conj                        none
% 19.77/2.99  --large_theory_mode                     true
% 19.77/2.99  --prolific_symb_bound                   200
% 19.77/2.99  --lt_threshold                          2000
% 19.77/2.99  --clause_weak_htbl                      true
% 19.77/2.99  --gc_record_bc_elim                     false
% 19.77/2.99  
% 19.77/2.99  ------ Preprocessing Options
% 19.77/2.99  
% 19.77/2.99  --preprocessing_flag                    true
% 19.77/2.99  --time_out_prep_mult                    0.1
% 19.77/2.99  --splitting_mode                        input
% 19.77/2.99  --splitting_grd                         true
% 19.77/2.99  --splitting_cvd                         false
% 19.77/2.99  --splitting_cvd_svl                     false
% 19.77/2.99  --splitting_nvd                         32
% 19.77/2.99  --sub_typing                            true
% 19.77/2.99  --prep_gs_sim                           false
% 19.77/2.99  --prep_unflatten                        true
% 19.77/2.99  --prep_res_sim                          true
% 19.77/2.99  --prep_upred                            true
% 19.77/2.99  --prep_sem_filter                       exhaustive
% 19.77/2.99  --prep_sem_filter_out                   false
% 19.77/2.99  --pred_elim                             false
% 19.77/2.99  --res_sim_input                         true
% 19.77/2.99  --eq_ax_congr_red                       true
% 19.77/2.99  --pure_diseq_elim                       true
% 19.77/2.99  --brand_transform                       false
% 19.77/2.99  --non_eq_to_eq                          false
% 19.77/2.99  --prep_def_merge                        true
% 19.77/2.99  --prep_def_merge_prop_impl              false
% 19.77/2.99  --prep_def_merge_mbd                    true
% 19.77/2.99  --prep_def_merge_tr_red                 false
% 19.77/2.99  --prep_def_merge_tr_cl                  false
% 19.77/2.99  --smt_preprocessing                     true
% 19.77/2.99  --smt_ac_axioms                         fast
% 19.77/2.99  --preprocessed_out                      false
% 19.77/2.99  --preprocessed_stats                    false
% 19.77/2.99  
% 19.77/2.99  ------ Abstraction refinement Options
% 19.77/2.99  
% 19.77/2.99  --abstr_ref                             []
% 19.77/2.99  --abstr_ref_prep                        false
% 19.77/2.99  --abstr_ref_until_sat                   false
% 19.77/2.99  --abstr_ref_sig_restrict                funpre
% 19.77/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/2.99  --abstr_ref_under                       []
% 19.77/2.99  
% 19.77/2.99  ------ SAT Options
% 19.77/2.99  
% 19.77/2.99  --sat_mode                              false
% 19.77/2.99  --sat_fm_restart_options                ""
% 19.77/2.99  --sat_gr_def                            false
% 19.77/2.99  --sat_epr_types                         true
% 19.77/2.99  --sat_non_cyclic_types                  false
% 19.77/2.99  --sat_finite_models                     false
% 19.77/2.99  --sat_fm_lemmas                         false
% 19.77/2.99  --sat_fm_prep                           false
% 19.77/2.99  --sat_fm_uc_incr                        true
% 19.77/2.99  --sat_out_model                         small
% 19.77/2.99  --sat_out_clauses                       false
% 19.77/2.99  
% 19.77/2.99  ------ QBF Options
% 19.77/2.99  
% 19.77/2.99  --qbf_mode                              false
% 19.77/2.99  --qbf_elim_univ                         false
% 19.77/2.99  --qbf_dom_inst                          none
% 19.77/2.99  --qbf_dom_pre_inst                      false
% 19.77/2.99  --qbf_sk_in                             false
% 19.77/2.99  --qbf_pred_elim                         true
% 19.77/2.99  --qbf_split                             512
% 19.77/2.99  
% 19.77/2.99  ------ BMC1 Options
% 19.77/2.99  
% 19.77/2.99  --bmc1_incremental                      false
% 19.77/2.99  --bmc1_axioms                           reachable_all
% 19.77/2.99  --bmc1_min_bound                        0
% 19.77/2.99  --bmc1_max_bound                        -1
% 19.77/2.99  --bmc1_max_bound_default                -1
% 19.77/2.99  --bmc1_symbol_reachability              true
% 19.77/2.99  --bmc1_property_lemmas                  false
% 19.77/2.99  --bmc1_k_induction                      false
% 19.77/2.99  --bmc1_non_equiv_states                 false
% 19.77/2.99  --bmc1_deadlock                         false
% 19.77/2.99  --bmc1_ucm                              false
% 19.77/2.99  --bmc1_add_unsat_core                   none
% 19.77/2.99  --bmc1_unsat_core_children              false
% 19.77/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/2.99  --bmc1_out_stat                         full
% 19.77/2.99  --bmc1_ground_init                      false
% 19.77/2.99  --bmc1_pre_inst_next_state              false
% 19.77/2.99  --bmc1_pre_inst_state                   false
% 19.77/2.99  --bmc1_pre_inst_reach_state             false
% 19.77/2.99  --bmc1_out_unsat_core                   false
% 19.77/2.99  --bmc1_aig_witness_out                  false
% 19.77/2.99  --bmc1_verbose                          false
% 19.77/2.99  --bmc1_dump_clauses_tptp                false
% 19.77/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.77/2.99  --bmc1_dump_file                        -
% 19.77/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.77/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.77/2.99  --bmc1_ucm_extend_mode                  1
% 19.77/2.99  --bmc1_ucm_init_mode                    2
% 19.77/2.99  --bmc1_ucm_cone_mode                    none
% 19.77/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.77/2.99  --bmc1_ucm_relax_model                  4
% 19.77/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.77/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/2.99  --bmc1_ucm_layered_model                none
% 19.77/2.99  --bmc1_ucm_max_lemma_size               10
% 19.77/2.99  
% 19.77/2.99  ------ AIG Options
% 19.77/2.99  
% 19.77/2.99  --aig_mode                              false
% 19.77/2.99  
% 19.77/2.99  ------ Instantiation Options
% 19.77/2.99  
% 19.77/2.99  --instantiation_flag                    true
% 19.77/2.99  --inst_sos_flag                         false
% 19.77/2.99  --inst_sos_phase                        true
% 19.77/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/2.99  --inst_lit_sel_side                     num_symb
% 19.77/2.99  --inst_solver_per_active                1400
% 19.77/2.99  --inst_solver_calls_frac                1.
% 19.77/2.99  --inst_passive_queue_type               priority_queues
% 19.77/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/2.99  --inst_passive_queues_freq              [25;2]
% 19.77/2.99  --inst_dismatching                      true
% 19.77/2.99  --inst_eager_unprocessed_to_passive     true
% 19.77/2.99  --inst_prop_sim_given                   true
% 19.77/2.99  --inst_prop_sim_new                     false
% 19.77/2.99  --inst_subs_new                         false
% 19.77/2.99  --inst_eq_res_simp                      false
% 19.77/2.99  --inst_subs_given                       false
% 19.77/2.99  --inst_orphan_elimination               true
% 19.77/2.99  --inst_learning_loop_flag               true
% 19.77/2.99  --inst_learning_start                   3000
% 19.77/2.99  --inst_learning_factor                  2
% 19.77/2.99  --inst_start_prop_sim_after_learn       3
% 19.77/2.99  --inst_sel_renew                        solver
% 19.77/2.99  --inst_lit_activity_flag                true
% 19.77/2.99  --inst_restr_to_given                   false
% 19.77/2.99  --inst_activity_threshold               500
% 19.77/2.99  --inst_out_proof                        true
% 19.77/2.99  
% 19.77/2.99  ------ Resolution Options
% 19.77/2.99  
% 19.77/2.99  --resolution_flag                       true
% 19.77/2.99  --res_lit_sel                           adaptive
% 19.77/2.99  --res_lit_sel_side                      none
% 19.77/2.99  --res_ordering                          kbo
% 19.77/2.99  --res_to_prop_solver                    active
% 19.77/2.99  --res_prop_simpl_new                    false
% 19.77/2.99  --res_prop_simpl_given                  true
% 19.77/2.99  --res_passive_queue_type                priority_queues
% 19.77/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/2.99  --res_passive_queues_freq               [15;5]
% 19.77/2.99  --res_forward_subs                      full
% 19.77/2.99  --res_backward_subs                     full
% 19.77/2.99  --res_forward_subs_resolution           true
% 19.77/2.99  --res_backward_subs_resolution          true
% 19.77/2.99  --res_orphan_elimination                true
% 19.77/2.99  --res_time_limit                        2.
% 19.77/2.99  --res_out_proof                         true
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Options
% 19.77/2.99  
% 19.77/2.99  --superposition_flag                    true
% 19.77/2.99  --sup_passive_queue_type                priority_queues
% 19.77/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/2.99  --sup_passive_queues_freq               [1;4]
% 19.77/2.99  --demod_completeness_check              fast
% 19.77/2.99  --demod_use_ground                      true
% 19.77/2.99  --sup_to_prop_solver                    passive
% 19.77/2.99  --sup_prop_simpl_new                    true
% 19.77/2.99  --sup_prop_simpl_given                  true
% 19.77/2.99  --sup_fun_splitting                     false
% 19.77/2.99  --sup_smt_interval                      50000
% 19.77/2.99  
% 19.77/2.99  ------ Superposition Simplification Setup
% 19.77/2.99  
% 19.77/2.99  --sup_indices_passive                   []
% 19.77/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.77/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_full_bw                           [BwDemod]
% 19.77/2.99  --sup_immed_triv                        [TrivRules]
% 19.77/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_immed_bw_main                     []
% 19.77/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.77/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.77/2.99  
% 19.77/2.99  ------ Combination Options
% 19.77/2.99  
% 19.77/2.99  --comb_res_mult                         3
% 19.77/2.99  --comb_sup_mult                         2
% 19.77/2.99  --comb_inst_mult                        10
% 19.77/2.99  
% 19.77/2.99  ------ Debug Options
% 19.77/2.99  
% 19.77/2.99  --dbg_backtrace                         false
% 19.77/2.99  --dbg_dump_prop_clauses                 false
% 19.77/2.99  --dbg_dump_prop_clauses_file            -
% 19.77/2.99  --dbg_out_stat                          false
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  ------ Proving...
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  % SZS status Theorem for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  fof(f13,conjecture,(
% 19.77/2.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f14,negated_conjecture,(
% 19.77/2.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 19.77/2.99    inference(negated_conjecture,[],[f13])).
% 19.77/2.99  
% 19.77/2.99  fof(f33,plain,(
% 19.77/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 19.77/2.99    inference(ennf_transformation,[],[f14])).
% 19.77/2.99  
% 19.77/2.99  fof(f34,plain,(
% 19.77/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 19.77/2.99    inference(flattening,[],[f33])).
% 19.77/2.99  
% 19.77/2.99  fof(f44,plain,(
% 19.77/2.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f43,plain,(
% 19.77/2.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f42,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f41,plain,(
% 19.77/2.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f40,plain,(
% 19.77/2.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f39,plain,(
% 19.77/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 19.77/2.99    introduced(choice_axiom,[])).
% 19.77/2.99  
% 19.77/2.99  fof(f45,plain,(
% 19.77/2.99    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 19.77/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f34,f44,f43,f42,f41,f40,f39])).
% 19.77/2.99  
% 19.77/2.99  fof(f73,plain,(
% 19.77/2.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f10,axiom,(
% 19.77/2.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f27,plain,(
% 19.77/2.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.77/2.99    inference(ennf_transformation,[],[f10])).
% 19.77/2.99  
% 19.77/2.99  fof(f28,plain,(
% 19.77/2.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.77/2.99    inference(flattening,[],[f27])).
% 19.77/2.99  
% 19.77/2.99  fof(f57,plain,(
% 19.77/2.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f28])).
% 19.77/2.99  
% 19.77/2.99  fof(f71,plain,(
% 19.77/2.99    v1_funct_1(sK4)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f69,plain,(
% 19.77/2.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f3,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f17,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.77/2.99    inference(ennf_transformation,[],[f3])).
% 19.77/2.99  
% 19.77/2.99  fof(f49,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f17])).
% 19.77/2.99  
% 19.77/2.99  fof(f76,plain,(
% 19.77/2.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f74,plain,(
% 19.77/2.99    v1_funct_1(sK5)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f11,axiom,(
% 19.77/2.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f29,plain,(
% 19.77/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 19.77/2.99    inference(ennf_transformation,[],[f11])).
% 19.77/2.99  
% 19.77/2.99  fof(f30,plain,(
% 19.77/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 19.77/2.99    inference(flattening,[],[f29])).
% 19.77/2.99  
% 19.77/2.99  fof(f37,plain,(
% 19.77/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 19.77/2.99    inference(nnf_transformation,[],[f30])).
% 19.77/2.99  
% 19.77/2.99  fof(f38,plain,(
% 19.77/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 19.77/2.99    inference(flattening,[],[f37])).
% 19.77/2.99  
% 19.77/2.99  fof(f58,plain,(
% 19.77/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f38])).
% 19.77/2.99  
% 19.77/2.99  fof(f81,plain,(
% 19.77/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(equality_resolution,[],[f58])).
% 19.77/2.99  
% 19.77/2.99  fof(f12,axiom,(
% 19.77/2.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f31,plain,(
% 19.77/2.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 19.77/2.99    inference(ennf_transformation,[],[f12])).
% 19.77/2.99  
% 19.77/2.99  fof(f32,plain,(
% 19.77/2.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 19.77/2.99    inference(flattening,[],[f31])).
% 19.77/2.99  
% 19.77/2.99  fof(f61,plain,(
% 19.77/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f32])).
% 19.77/2.99  
% 19.77/2.99  fof(f62,plain,(
% 19.77/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f32])).
% 19.77/2.99  
% 19.77/2.99  fof(f63,plain,(
% 19.77/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f32])).
% 19.77/2.99  
% 19.77/2.99  fof(f65,plain,(
% 19.77/2.99    ~v1_xboole_0(sK1)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f68,plain,(
% 19.77/2.99    ~v1_xboole_0(sK3)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f75,plain,(
% 19.77/2.99    v1_funct_2(sK5,sK3,sK1)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f64,plain,(
% 19.77/2.99    ~v1_xboole_0(sK0)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f70,plain,(
% 19.77/2.99    r1_subset_1(sK2,sK3)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f7,axiom,(
% 19.77/2.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f23,plain,(
% 19.77/2.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 19.77/2.99    inference(ennf_transformation,[],[f7])).
% 19.77/2.99  
% 19.77/2.99  fof(f24,plain,(
% 19.77/2.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 19.77/2.99    inference(flattening,[],[f23])).
% 19.77/2.99  
% 19.77/2.99  fof(f36,plain,(
% 19.77/2.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 19.77/2.99    inference(nnf_transformation,[],[f24])).
% 19.77/2.99  
% 19.77/2.99  fof(f53,plain,(
% 19.77/2.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f36])).
% 19.77/2.99  
% 19.77/2.99  fof(f66,plain,(
% 19.77/2.99    ~v1_xboole_0(sK2)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f1,axiom,(
% 19.77/2.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f35,plain,(
% 19.77/2.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 19.77/2.99    inference(nnf_transformation,[],[f1])).
% 19.77/2.99  
% 19.77/2.99  fof(f46,plain,(
% 19.77/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f35])).
% 19.77/2.99  
% 19.77/2.99  fof(f8,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f25,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.77/2.99    inference(ennf_transformation,[],[f8])).
% 19.77/2.99  
% 19.77/2.99  fof(f55,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f25])).
% 19.77/2.99  
% 19.77/2.99  fof(f4,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f18,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.77/2.99    inference(ennf_transformation,[],[f4])).
% 19.77/2.99  
% 19.77/2.99  fof(f50,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f18])).
% 19.77/2.99  
% 19.77/2.99  fof(f5,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f19,plain,(
% 19.77/2.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 19.77/2.99    inference(ennf_transformation,[],[f5])).
% 19.77/2.99  
% 19.77/2.99  fof(f20,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 19.77/2.99    inference(flattening,[],[f19])).
% 19.77/2.99  
% 19.77/2.99  fof(f51,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f20])).
% 19.77/2.99  
% 19.77/2.99  fof(f72,plain,(
% 19.77/2.99    v1_funct_2(sK4,sK2,sK1)),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f67,plain,(
% 19.77/2.99    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f59,plain,(
% 19.77/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(cnf_transformation,[],[f38])).
% 19.77/2.99  
% 19.77/2.99  fof(f80,plain,(
% 19.77/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 19.77/2.99    inference(equality_resolution,[],[f59])).
% 19.77/2.99  
% 19.77/2.99  fof(f77,plain,(
% 19.77/2.99    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 19.77/2.99    inference(cnf_transformation,[],[f45])).
% 19.77/2.99  
% 19.77/2.99  fof(f2,axiom,(
% 19.77/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 19.77/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.99  
% 19.77/2.99  fof(f16,plain,(
% 19.77/2.99    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 19.77/2.99    inference(ennf_transformation,[],[f2])).
% 19.77/2.99  
% 19.77/2.99  fof(f48,plain,(
% 19.77/2.99    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 19.77/2.99    inference(cnf_transformation,[],[f16])).
% 19.77/2.99  
% 19.77/2.99  fof(f47,plain,(
% 19.77/2.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.77/2.99    inference(cnf_transformation,[],[f35])).
% 19.77/2.99  
% 19.77/2.99  cnf(c_22,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 19.77/2.99      inference(cnf_transformation,[],[f73]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_372,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_22]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1145,plain,
% 19.77/2.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_11,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 19.77/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_381,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.77/2.99      | ~ v1_funct_1(X0_51)
% 19.77/2.99      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_11]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1137,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2455,plain,
% 19.77/2.99      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1145,c_1137]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24,negated_conjecture,
% 19.77/2.99      ( v1_funct_1(sK4) ),
% 19.77/2.99      inference(cnf_transformation,[],[f71]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1627,plain,
% 19.77/2.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 19.77/2.99      | ~ v1_funct_1(sK4)
% 19.77/2.99      | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_381]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1858,plain,
% 19.77/2.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.77/2.99      | ~ v1_funct_1(sK4)
% 19.77/2.99      | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_1627]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6610,plain,
% 19.77/2.99      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_2455,c_24,c_22,c_1858]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_26,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_368,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_26]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1149,plain,
% 19.77/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.77/2.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_389,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 19.77/2.99      | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_3]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1129,plain,
% 19.77/2.99      ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1886,plain,
% 19.77/2.99      ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1149,c_1129]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_19,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 19.77/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_375,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_19]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1142,plain,
% 19.77/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2454,plain,
% 19.77/2.99      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
% 19.77/2.99      | v1_funct_1(sK5) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1142,c_1137]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_21,negated_conjecture,
% 19.77/2.99      ( v1_funct_1(sK5) ),
% 19.77/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1622,plain,
% 19.77/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 19.77/2.99      | ~ v1_funct_1(sK5)
% 19.77/2.99      | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_381]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1853,plain,
% 19.77/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 19.77/2.99      | ~ v1_funct_1(sK5)
% 19.77/2.99      | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_1622]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6204,plain,
% 19.77/2.99      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_2454,c_21,c_19,c_1853]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_14,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 19.77/2.99      inference(cnf_transformation,[],[f81]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_17,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_16,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_15,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_329,plain,
% 19.77/2.99      ( ~ v1_funct_1(X3)
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_14,c_17,c_16,c_15]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_330,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | v1_xboole_0(X1)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_329]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_362,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 19.77/2.99      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 19.77/2.99      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.77/2.99      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 19.77/2.99      | ~ v1_funct_1(X0_51)
% 19.77/2.99      | ~ v1_funct_1(X3_51)
% 19.77/2.99      | v1_xboole_0(X1_51)
% 19.77/2.99      | v1_xboole_0(X2_51)
% 19.77/2.99      | v1_xboole_0(X4_51)
% 19.77/2.99      | v1_xboole_0(X5_51)
% 19.77/2.99      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_330]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1155,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
% 19.77/2.99      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X5_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X3_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X4_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6209,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_funct_1(sK5) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK1) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6204,c_1155]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_30,negated_conjecture,
% 19.77/2.99      ( ~ v1_xboole_0(sK1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_33,plain,
% 19.77/2.99      ( v1_xboole_0(sK1) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_27,negated_conjecture,
% 19.77/2.99      ( ~ v1_xboole_0(sK3) ),
% 19.77/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_36,plain,
% 19.77/2.99      ( v1_xboole_0(sK3) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_42,plain,
% 19.77/2.99      ( v1_funct_1(sK5) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_20,negated_conjecture,
% 19.77/2.99      ( v1_funct_2(sK5,sK3,sK1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f75]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_43,plain,
% 19.77/2.99      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_44,plain,
% 19.77/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_29741,plain,
% 19.77/2.99      ( v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_6209,c_33,c_36,c_42,c_43,c_44]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_29742,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_29741]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_29762,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1886,c_29742]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_29852,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_29762,c_1886]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_31,negated_conjecture,
% 19.77/2.99      ( ~ v1_xboole_0(sK0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_32,plain,
% 19.77/2.99      ( v1_xboole_0(sK0) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_37,plain,
% 19.77/2.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51622,plain,
% 19.77/2.99      ( v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_29852,c_32,c_37]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51623,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_51622]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51636,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 19.77/2.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6610,c_51623]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_25,negated_conjecture,
% 19.77/2.99      ( r1_subset_1(sK2,sK3) ),
% 19.77/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_369,negated_conjecture,
% 19.77/2.99      ( r1_subset_1(sK2,sK3) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_25]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1148,plain,
% 19.77/2.99      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8,plain,
% 19.77/2.99      ( ~ r1_subset_1(X0,X1)
% 19.77/2.99      | r1_xboole_0(X0,X1)
% 19.77/2.99      | v1_xboole_0(X0)
% 19.77/2.99      | v1_xboole_0(X1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_384,plain,
% 19.77/2.99      ( ~ r1_subset_1(X0_51,X1_51)
% 19.77/2.99      | r1_xboole_0(X0_51,X1_51)
% 19.77/2.99      | v1_xboole_0(X1_51)
% 19.77/2.99      | v1_xboole_0(X0_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_8]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1134,plain,
% 19.77/2.99      ( r1_subset_1(X0_51,X1_51) != iProver_top
% 19.77/2.99      | r1_xboole_0(X0_51,X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2230,plain,
% 19.77/2.99      ( r1_xboole_0(sK2,sK3) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1148,c_1134]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_29,negated_conjecture,
% 19.77/2.99      ( ~ v1_xboole_0(sK2) ),
% 19.77/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_34,plain,
% 19.77/2.99      ( v1_xboole_0(sK2) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_38,plain,
% 19.77/2.99      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1553,plain,
% 19.77/2.99      ( ~ r1_subset_1(sK2,sK3)
% 19.77/2.99      | r1_xboole_0(sK2,sK3)
% 19.77/2.99      | v1_xboole_0(sK3)
% 19.77/2.99      | v1_xboole_0(sK2) ),
% 19.77/2.99      inference(instantiation,[status(thm)],[c_384]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1554,plain,
% 19.77/2.99      ( r1_subset_1(sK2,sK3) != iProver_top
% 19.77/2.99      | r1_xboole_0(sK2,sK3) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_1553]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5332,plain,
% 19.77/2.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_2230,c_34,c_36,c_38,c_1554]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_391,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0_51,X1_51)
% 19.77/2.99      | k3_xboole_0(X0_51,X1_51) = k1_xboole_0 ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_1]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1127,plain,
% 19.77/2.99      ( k3_xboole_0(X0_51,X1_51) = k1_xboole_0
% 19.77/2.99      | r1_xboole_0(X0_51,X1_51) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5337,plain,
% 19.77/2.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_5332,c_1127]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | v1_relat_1(X0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_383,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.77/2.99      | v1_relat_1(X0_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_9]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1135,plain,
% 19.77/2.99      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 19.77/2.99      | v1_relat_1(X0_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2150,plain,
% 19.77/2.99      ( v1_relat_1(sK5) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1142,c_1135]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_4,plain,
% 19.77/2.99      ( ~ v1_relat_1(X0)
% 19.77/2.99      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_388,plain,
% 19.77/2.99      ( ~ v1_relat_1(X0_51)
% 19.77/2.99      | k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51)) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_4]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1130,plain,
% 19.77/2.99      ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51))
% 19.77/2.99      | v1_relat_1(X0_51) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3220,plain,
% 19.77/2.99      ( k7_relat_1(sK5,k3_xboole_0(X0_51,X1_51)) = k7_relat_1(k7_relat_1(sK5,X0_51),X1_51) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_2150,c_1130]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0,X1)
% 19.77/2.99      | ~ v1_relat_1(X2)
% 19.77/2.99      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_387,plain,
% 19.77/2.99      ( ~ r1_xboole_0(X0_51,X1_51)
% 19.77/2.99      | ~ v1_relat_1(X2_51)
% 19.77/2.99      | k7_relat_1(k7_relat_1(X2_51,X0_51),X1_51) = k1_xboole_0 ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_5]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1131,plain,
% 19.77/2.99      ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
% 19.77/2.99      | r1_xboole_0(X1_51,X2_51) != iProver_top
% 19.77/2.99      | v1_relat_1(X0_51) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5339,plain,
% 19.77/2.99      ( k7_relat_1(k7_relat_1(X0_51,sK2),sK3) = k1_xboole_0
% 19.77/2.99      | v1_relat_1(X0_51) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_5332,c_1131]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5820,plain,
% 19.77/2.99      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_2150,c_5339]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_23649,plain,
% 19.77/2.99      ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_3220,c_5820]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_23651,plain,
% 19.77/2.99      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_23649,c_5337]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51720,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 19.77/2.99      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(light_normalisation,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_51636,c_5337,c_23651]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_379,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 19.77/2.99      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 19.77/2.99      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.77/2.99      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 19.77/2.99      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
% 19.77/2.99      | ~ v1_funct_1(X0_51)
% 19.77/2.99      | ~ v1_funct_1(X3_51)
% 19.77/2.99      | v1_xboole_0(X1_51)
% 19.77/2.99      | v1_xboole_0(X2_51)
% 19.77/2.99      | v1_xboole_0(X4_51)
% 19.77/2.99      | v1_xboole_0(X5_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_15]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1139,plain,
% 19.77/2.99      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
% 19.77/2.99      | v1_funct_1(X0_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X3_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X5_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X4_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2830,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 19.77/2.99      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 19.77/2.99      | v1_funct_1(X5_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X4_51) != iProver_top
% 19.77/2.99      | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X3_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1139,c_1137]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_377,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 19.77/2.99      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 19.77/2.99      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.77/2.99      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 19.77/2.99      | ~ v1_funct_1(X0_51)
% 19.77/2.99      | ~ v1_funct_1(X3_51)
% 19.77/2.99      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
% 19.77/2.99      | v1_xboole_0(X1_51)
% 19.77/2.99      | v1_xboole_0(X2_51)
% 19.77/2.99      | v1_xboole_0(X4_51)
% 19.77/2.99      | v1_xboole_0(X5_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_17]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1141,plain,
% 19.77/2.99      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 19.77/2.99      | v1_funct_1(X0_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X3_51) != iProver_top
% 19.77/2.99      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
% 19.77/2.99      | v1_xboole_0(X5_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X4_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7814,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 19.77/2.99      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 19.77/2.99      | v1_funct_1(X5_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X4_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X3_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(forward_subsumption_resolution,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_2830,c_1141]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_7818,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 19.77/2.99      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 19.77/2.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_funct_1(sK5) != iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK1) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1142,c_7814]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8979,plain,
% 19.77/2.99      ( v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 19.77/2.99      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_7818,c_33,c_36,c_42,c_43]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8980,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 19.77/2.99      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_8979]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_8994,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1145,c_8980]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_39,plain,
% 19.77/2.99      ( v1_funct_1(sK4) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_23,negated_conjecture,
% 19.77/2.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 19.77/2.99      inference(cnf_transformation,[],[f72]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_40,plain,
% 19.77/2.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9459,plain,
% 19.77/2.99      ( v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_8994,c_34,c_39,c_40]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9460,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_9459]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9469,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1149,c_9460]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_28,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_35,plain,
% 19.77/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9600,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_9469,c_32,c_35]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51721,plain,
% 19.77/2.99      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 19.77/2.99      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_51720,c_9600]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_13,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f80]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_338,plain,
% 19.77/2.99      ( ~ v1_funct_1(X3)
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X1)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_13,c_17,c_16,c_15]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_339,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 19.77/2.99      | ~ v1_funct_2(X3,X4,X2)
% 19.77/2.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 19.77/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.77/2.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 19.77/2.99      | ~ v1_funct_1(X0)
% 19.77/2.99      | ~ v1_funct_1(X3)
% 19.77/2.99      | v1_xboole_0(X1)
% 19.77/2.99      | v1_xboole_0(X2)
% 19.77/2.99      | v1_xboole_0(X4)
% 19.77/2.99      | v1_xboole_0(X5)
% 19.77/2.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_338]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_361,plain,
% 19.77/2.99      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 19.77/2.99      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 19.77/2.99      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 19.77/2.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 19.77/2.99      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 19.77/2.99      | ~ v1_funct_1(X0_51)
% 19.77/2.99      | ~ v1_funct_1(X3_51)
% 19.77/2.99      | v1_xboole_0(X1_51)
% 19.77/2.99      | v1_xboole_0(X2_51)
% 19.77/2.99      | v1_xboole_0(X4_51)
% 19.77/2.99      | v1_xboole_0(X5_51)
% 19.77/2.99      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_339]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1156,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
% 19.77/2.99      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X5_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X3_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X4_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_361]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6208,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_funct_1(sK5) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK1) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6204,c_1156]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_28833,plain,
% 19.77/2.99      ( v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_6208,c_33,c_36,c_42,c_43,c_44]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_28834,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X2_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_28833]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_28854,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1886,c_28834]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_28944,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_28854,c_1886]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3623,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(sK0,X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
% 19.77/2.99      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X3_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1886,c_1156]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3739,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,X1_51,X2_51,k3_xboole_0(X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
% 19.77/2.99      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X3_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK3) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK0) = iProver_top ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_3623,c_1886]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_13276,plain,
% 19.77/2.99      ( m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
% 19.77/2.99      | k2_partfun1(X0_51,X1_51,X2_51,k3_xboole_0(X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | v1_funct_1(X3_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_3739,c_32,c_36,c_37]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_13277,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,X1_51,X2_51,k3_xboole_0(X0_51,sK3)) != k2_partfun1(sK3,X1_51,X3_51,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),X1_51,k1_tmap_1(sK0,X1_51,X0_51,sK3,X2_51,X3_51),sK3) = X3_51
% 19.77/2.99      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 19.77/2.99      | v1_funct_2(X3_51,sK3,X1_51) != iProver_top
% 19.77/2.99      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_51))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X3_51) != iProver_top
% 19.77/2.99      | v1_funct_1(X2_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X1_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_13276]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_13299,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_funct_1(sK5) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_xboole_0(sK1) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6204,c_13277]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51250,plain,
% 19.77/2.99      ( v1_xboole_0(X0_51) = iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
% 19.77/2.99      inference(global_propositional_subsumption,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_28944,c_32,c_37]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51251,plain,
% 19.77/2.99      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 19.77/2.99      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(X1_51) != iProver_top
% 19.77/2.99      | v1_xboole_0(X0_51) = iProver_top ),
% 19.77/2.99      inference(renaming,[status(thm)],[c_51250]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51264,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 19.77/2.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_6610,c_51251]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51348,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 19.77/2.99      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(light_normalisation,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_51264,c_5337,c_23651]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_51349,plain,
% 19.77/2.99      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 19.77/2.99      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0
% 19.77/2.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 19.77/2.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.77/2.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 19.77/2.99      | v1_funct_1(sK4) != iProver_top
% 19.77/2.99      | v1_xboole_0(sK2) = iProver_top ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_51348,c_9600]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_18,negated_conjecture,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 19.77/2.99      inference(cnf_transformation,[],[f77]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_376,negated_conjecture,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_18]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3621,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_1886,c_376]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_5815,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_5337,c_3621]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_6742,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_5815,c_6204,c_6610]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9604,plain,
% 19.77/2.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_9600,c_6742]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_9605,plain,
% 19.77/2.99      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_9604,c_9600]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_43509,plain,
% 19.77/2.99      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 19.77/2.99      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 19.77/2.99      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_9605,c_23651]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2151,plain,
% 19.77/2.99      ( v1_relat_1(sK4) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1145,c_1135]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_3336,plain,
% 19.77/2.99      ( k7_relat_1(sK4,k3_xboole_0(X0_51,X1_51)) = k7_relat_1(k7_relat_1(sK4,X0_51),X1_51) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_2151,c_1130]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_2,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.77/2.99      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 19.77/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_390,plain,
% 19.77/2.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 19.77/2.99      | k9_subset_1(X1_51,X0_51,X2_51) = k9_subset_1(X1_51,X2_51,X0_51) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_2]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1128,plain,
% 19.77/2.99      ( k9_subset_1(X0_51,X1_51,X2_51) = k9_subset_1(X0_51,X2_51,X1_51)
% 19.77/2.99      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_390]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1887,plain,
% 19.77/2.99      ( k9_subset_1(sK0,sK3,X0_51) = k9_subset_1(sK0,X0_51,sK3) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1149,c_1128]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1891,plain,
% 19.77/2.99      ( k9_subset_1(sK0,sK3,X0_51) = k3_xboole_0(X0_51,sK3) ),
% 19.77/2.99      inference(demodulation,[status(thm)],[c_1886,c_1887]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_366,negated_conjecture,
% 19.77/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_28]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1151,plain,
% 19.77/2.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1899,plain,
% 19.77/2.99      ( k9_subset_1(sK0,X0_51,sK2) = k3_xboole_0(X0_51,sK2) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1151,c_1129]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_4493,plain,
% 19.77/2.99      ( k3_xboole_0(sK3,sK2) = k3_xboole_0(sK2,sK3) ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_1891,c_1899]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_17769,plain,
% 19.77/2.99      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_4493,c_5337]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_0,plain,
% 19.77/2.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.77/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_392,plain,
% 19.77/2.99      ( r1_xboole_0(X0_51,X1_51)
% 19.77/2.99      | k3_xboole_0(X0_51,X1_51) != k1_xboole_0 ),
% 19.77/2.99      inference(subtyping,[status(esa)],[c_0]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_1126,plain,
% 19.77/2.99      ( k3_xboole_0(X0_51,X1_51) != k1_xboole_0
% 19.77/2.99      | r1_xboole_0(X0_51,X1_51) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_17771,plain,
% 19.77/2.99      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_17769,c_1126]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_17870,plain,
% 19.77/2.99      ( k7_relat_1(k7_relat_1(X0_51,sK3),sK2) = k1_xboole_0
% 19.77/2.99      | v1_relat_1(X0_51) != iProver_top ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_17771,c_1131]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_18012,plain,
% 19.77/2.99      ( k7_relat_1(k7_relat_1(sK4,sK3),sK2) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_2151,c_17870]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24057,plain,
% 19.77/2.99      ( k7_relat_1(sK4,k3_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 19.77/2.99      inference(superposition,[status(thm)],[c_3336,c_18012]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_24059,plain,
% 19.77/2.99      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 19.77/2.99      inference(light_normalisation,[status(thm)],[c_24057,c_17769]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(c_41,plain,
% 19.77/2.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 19.77/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.77/2.99  
% 19.77/2.99  cnf(contradiction,plain,
% 19.77/2.99      ( $false ),
% 19.77/2.99      inference(minisat,
% 19.77/2.99                [status(thm)],
% 19.77/2.99                [c_51721,c_51349,c_43509,c_24059,c_41,c_40,c_39,c_35,
% 19.77/2.99                 c_34]) ).
% 19.77/2.99  
% 19.77/2.99  
% 19.77/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.77/2.99  
% 19.77/2.99  ------                               Statistics
% 19.77/2.99  
% 19.77/2.99  ------ Selected
% 19.77/2.99  
% 19.77/2.99  total_time:                             2.388
% 19.77/2.99  
%------------------------------------------------------------------------------
