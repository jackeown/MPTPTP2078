%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:22 EST 2020

% Result     : Theorem 7.09s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  245 (5552 expanded)
%              Number of clauses        :  161 (1464 expanded)
%              Number of leaves         :   22 (1795 expanded)
%              Depth                    :   28
%              Number of atoms          : 1256 (54993 expanded)
%              Number of equality atoms :  458 (12188 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f50,f49,f48,f47,f46,f45])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f76,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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
    inference(cnf_transformation,[],[f44])).

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

fof(f77,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_759,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1276,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_777,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1259,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_777])).

cnf(c_2135,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1276,c_1259])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_763,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1272,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_772,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1264,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_2592,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_1264])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2886,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2592,c_43])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_766,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1269,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_2591,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1264])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2881,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_46])).

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
    inference(cnf_transformation,[],[f91])).

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
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_193,plain,
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

cnf(c_194,plain,
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
    inference(renaming,[status(thm)],[c_193])).

cnf(c_752,plain,
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
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_1283,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_3820,plain,
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
    inference(superposition,[status(thm)],[c_2881,c_1283])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7055,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3820,c_37,c_40,c_46,c_47,c_48])).

cnf(c_7056,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_7055])).

cnf(c_7062,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_7056])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_776,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1448,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_53))
    | ~ v1_xboole_0(X0_53)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1449,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1448])).

cnf(c_7072,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7062,c_38,c_43,c_44,c_45,c_1449])).

cnf(c_7073,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7072])).

cnf(c_7078,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_7073])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_760,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1275,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_774,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_subset_1(X1_53,X0_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1262,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_subset_1(X1_53,X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_2588,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_1262])).

cnf(c_42,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1447,plain,
    ( r1_subset_1(X0_53,sK2)
    | ~ r1_subset_1(sK2,X0_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1630,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ r1_subset_1(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1447])).

cnf(c_1631,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1630])).

cnf(c_3117,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2588,c_38,c_40,c_42,c_1631])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_362,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_14,c_10,c_9])).

cnf(c_367,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_366])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_367])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_14,c_11,c_10,c_9])).

cnf(c_442,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_441])).

cnf(c_751,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_442])).

cnf(c_1284,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_4694,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_1284])).

cnf(c_1394,plain,
    ( ~ v1_funct_2(X0_53,X1_53,sK1)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(sK1)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_1664,plain,
    ( ~ v1_funct_2(sK4,X0_53,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1666,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_4805,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4694,c_34,c_28,c_27,c_26,c_1666])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_470,plain,
    ( ~ r1_subset_1(X0,X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X0 != X3
    | k7_relat_1(X2,X3) = k1_xboole_0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_471,plain,
    ( ~ r1_subset_1(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X1))
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_750,plain,
    ( ~ r1_subset_1(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(k1_relat_1(X1_53))
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_471])).

cnf(c_1285,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_subset_1(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_5026,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4805,c_1285])).

cnf(c_5027,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5026,c_4805])).

cnf(c_773,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1825,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1826,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1825])).

cnf(c_6470,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5027,c_38,c_45,c_1826])).

cnf(c_6471,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_6470])).

cnf(c_6476,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3117,c_6471])).

cnf(c_6508,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6476,c_40])).

cnf(c_1263,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_2499,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1272,c_1263])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_775,plain,
    ( ~ v1_relat_1(X0_53)
    | k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1261,plain,
    ( k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_2659,plain,
    ( k3_xboole_0(k7_relat_1(sK4,X0_53),k7_relat_1(sK4,X1_53)) = k7_relat_1(sK4,k3_xboole_0(X0_53,X1_53)) ),
    inference(superposition,[status(thm)],[c_2499,c_1261])).

cnf(c_6513,plain,
    ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k3_xboole_0(k7_relat_1(sK4,X0_53),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6508,c_2659])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_778,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_6514,plain,
    ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6513,c_778])).

cnf(c_4693,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1284])).

cnf(c_1659,plain,
    ( ~ v1_funct_2(sK5,X0_53,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_2096,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_4774,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4693,c_34,c_25,c_24,c_23,c_2096])).

cnf(c_5025,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4774,c_1285])).

cnf(c_5028,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5025,c_4774])).

cnf(c_1822,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_773])).

cnf(c_1823,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1822])).

cnf(c_6521,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5028,c_40,c_48,c_1823])).

cnf(c_6522,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_6521])).

cnf(c_6527,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_6522])).

cnf(c_5033,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5028])).

cnf(c_6588,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6527,c_38,c_40,c_42,c_48,c_1823,c_5033])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_779,plain,
    ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2498,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1263])).

cnf(c_2656,plain,
    ( k3_xboole_0(k7_relat_1(sK5,X0_53),k7_relat_1(sK5,X1_53)) = k7_relat_1(sK5,k3_xboole_0(X0_53,X1_53)) ),
    inference(superposition,[status(thm)],[c_2498,c_1261])).

cnf(c_3101,plain,
    ( k3_xboole_0(k7_relat_1(sK5,X0_53),k7_relat_1(sK5,X1_53)) = k7_relat_1(sK5,k3_xboole_0(X1_53,X0_53)) ),
    inference(superposition,[status(thm)],[c_779,c_2656])).

cnf(c_6592,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k3_xboole_0(k7_relat_1(sK5,X0_53),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6588,c_3101])).

cnf(c_6595,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6592,c_778])).

cnf(c_7079,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7078,c_2135,c_6514,c_6595])).

cnf(c_7080,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7079])).

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
    inference(cnf_transformation,[],[f92])).

cnf(c_186,plain,
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

cnf(c_187,plain,
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
    inference(renaming,[status(thm)],[c_186])).

cnf(c_753,plain,
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
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_1282,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_3320,plain,
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
    inference(superposition,[status(thm)],[c_2881,c_1282])).

cnf(c_3546,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3320,c_37,c_40,c_46,c_47,c_48])).

cnf(c_3547,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_3546])).

cnf(c_3553,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2886,c_3547])).

cnf(c_3586,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3553,c_38,c_43,c_44,c_45,c_1449])).

cnf(c_3587,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3586])).

cnf(c_3592,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_3587])).

cnf(c_3593,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3592,c_2135])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3594,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3593])).

cnf(c_3656,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3593,c_32,c_30,c_3594])).

cnf(c_6928,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6514,c_3656])).

cnf(c_6932,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6928,c_6595])).

cnf(c_6933,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_6932])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_767,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2309,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2135,c_767])).

cnf(c_2884,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2881,c_2309])).

cnf(c_3105,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2884,c_2886])).

cnf(c_6929,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6514,c_3105])).

cnf(c_6930,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6929,c_6595])).

cnf(c_6931,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_6930])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7080,c_6933,c_6931,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.09/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/1.50  
% 7.09/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.09/1.50  
% 7.09/1.50  ------  iProver source info
% 7.09/1.50  
% 7.09/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.09/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.09/1.50  git: non_committed_changes: false
% 7.09/1.50  git: last_make_outside_of_git: false
% 7.09/1.50  
% 7.09/1.50  ------ 
% 7.09/1.50  
% 7.09/1.50  ------ Input Options
% 7.09/1.50  
% 7.09/1.50  --out_options                           all
% 7.09/1.50  --tptp_safe_out                         true
% 7.09/1.50  --problem_path                          ""
% 7.09/1.50  --include_path                          ""
% 7.09/1.50  --clausifier                            res/vclausify_rel
% 7.09/1.50  --clausifier_options                    ""
% 7.09/1.50  --stdin                                 false
% 7.09/1.50  --stats_out                             all
% 7.09/1.50  
% 7.09/1.50  ------ General Options
% 7.09/1.50  
% 7.09/1.50  --fof                                   false
% 7.09/1.50  --time_out_real                         305.
% 7.09/1.50  --time_out_virtual                      -1.
% 7.09/1.50  --symbol_type_check                     false
% 7.09/1.50  --clausify_out                          false
% 7.09/1.50  --sig_cnt_out                           false
% 7.09/1.50  --trig_cnt_out                          false
% 7.09/1.50  --trig_cnt_out_tolerance                1.
% 7.09/1.50  --trig_cnt_out_sk_spl                   false
% 7.09/1.50  --abstr_cl_out                          false
% 7.09/1.50  
% 7.09/1.50  ------ Global Options
% 7.09/1.50  
% 7.09/1.50  --schedule                              default
% 7.09/1.50  --add_important_lit                     false
% 7.09/1.50  --prop_solver_per_cl                    1000
% 7.09/1.50  --min_unsat_core                        false
% 7.09/1.50  --soft_assumptions                      false
% 7.09/1.50  --soft_lemma_size                       3
% 7.09/1.50  --prop_impl_unit_size                   0
% 7.09/1.50  --prop_impl_unit                        []
% 7.09/1.50  --share_sel_clauses                     true
% 7.09/1.50  --reset_solvers                         false
% 7.09/1.50  --bc_imp_inh                            [conj_cone]
% 7.09/1.50  --conj_cone_tolerance                   3.
% 7.09/1.50  --extra_neg_conj                        none
% 7.09/1.50  --large_theory_mode                     true
% 7.09/1.50  --prolific_symb_bound                   200
% 7.09/1.50  --lt_threshold                          2000
% 7.09/1.50  --clause_weak_htbl                      true
% 7.09/1.50  --gc_record_bc_elim                     false
% 7.09/1.50  
% 7.09/1.50  ------ Preprocessing Options
% 7.09/1.50  
% 7.09/1.50  --preprocessing_flag                    true
% 7.09/1.50  --time_out_prep_mult                    0.1
% 7.09/1.50  --splitting_mode                        input
% 7.09/1.50  --splitting_grd                         true
% 7.09/1.50  --splitting_cvd                         false
% 7.09/1.50  --splitting_cvd_svl                     false
% 7.09/1.50  --splitting_nvd                         32
% 7.09/1.50  --sub_typing                            true
% 7.09/1.50  --prep_gs_sim                           true
% 7.09/1.50  --prep_unflatten                        true
% 7.09/1.50  --prep_res_sim                          true
% 7.09/1.50  --prep_upred                            true
% 7.09/1.50  --prep_sem_filter                       exhaustive
% 7.09/1.50  --prep_sem_filter_out                   false
% 7.09/1.50  --pred_elim                             true
% 7.09/1.50  --res_sim_input                         true
% 7.09/1.50  --eq_ax_congr_red                       true
% 7.09/1.50  --pure_diseq_elim                       true
% 7.09/1.50  --brand_transform                       false
% 7.09/1.50  --non_eq_to_eq                          false
% 7.09/1.50  --prep_def_merge                        true
% 7.09/1.50  --prep_def_merge_prop_impl              false
% 7.09/1.50  --prep_def_merge_mbd                    true
% 7.09/1.50  --prep_def_merge_tr_red                 false
% 7.09/1.50  --prep_def_merge_tr_cl                  false
% 7.09/1.50  --smt_preprocessing                     true
% 7.09/1.50  --smt_ac_axioms                         fast
% 7.09/1.50  --preprocessed_out                      false
% 7.09/1.50  --preprocessed_stats                    false
% 7.09/1.50  
% 7.09/1.50  ------ Abstraction refinement Options
% 7.09/1.50  
% 7.09/1.50  --abstr_ref                             []
% 7.09/1.50  --abstr_ref_prep                        false
% 7.09/1.50  --abstr_ref_until_sat                   false
% 7.09/1.50  --abstr_ref_sig_restrict                funpre
% 7.09/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.09/1.50  --abstr_ref_under                       []
% 7.09/1.50  
% 7.09/1.50  ------ SAT Options
% 7.09/1.50  
% 7.09/1.50  --sat_mode                              false
% 7.09/1.50  --sat_fm_restart_options                ""
% 7.09/1.50  --sat_gr_def                            false
% 7.09/1.50  --sat_epr_types                         true
% 7.09/1.50  --sat_non_cyclic_types                  false
% 7.09/1.50  --sat_finite_models                     false
% 7.09/1.50  --sat_fm_lemmas                         false
% 7.09/1.50  --sat_fm_prep                           false
% 7.09/1.50  --sat_fm_uc_incr                        true
% 7.09/1.50  --sat_out_model                         small
% 7.09/1.50  --sat_out_clauses                       false
% 7.09/1.50  
% 7.09/1.50  ------ QBF Options
% 7.09/1.50  
% 7.09/1.50  --qbf_mode                              false
% 7.09/1.50  --qbf_elim_univ                         false
% 7.09/1.50  --qbf_dom_inst                          none
% 7.09/1.50  --qbf_dom_pre_inst                      false
% 7.09/1.50  --qbf_sk_in                             false
% 7.09/1.50  --qbf_pred_elim                         true
% 7.09/1.50  --qbf_split                             512
% 7.09/1.50  
% 7.09/1.50  ------ BMC1 Options
% 7.09/1.50  
% 7.09/1.50  --bmc1_incremental                      false
% 7.09/1.50  --bmc1_axioms                           reachable_all
% 7.09/1.50  --bmc1_min_bound                        0
% 7.09/1.50  --bmc1_max_bound                        -1
% 7.09/1.50  --bmc1_max_bound_default                -1
% 7.09/1.50  --bmc1_symbol_reachability              true
% 7.09/1.50  --bmc1_property_lemmas                  false
% 7.09/1.50  --bmc1_k_induction                      false
% 7.09/1.50  --bmc1_non_equiv_states                 false
% 7.09/1.50  --bmc1_deadlock                         false
% 7.09/1.50  --bmc1_ucm                              false
% 7.09/1.50  --bmc1_add_unsat_core                   none
% 7.09/1.50  --bmc1_unsat_core_children              false
% 7.09/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.09/1.50  --bmc1_out_stat                         full
% 7.09/1.50  --bmc1_ground_init                      false
% 7.09/1.50  --bmc1_pre_inst_next_state              false
% 7.09/1.50  --bmc1_pre_inst_state                   false
% 7.09/1.50  --bmc1_pre_inst_reach_state             false
% 7.09/1.50  --bmc1_out_unsat_core                   false
% 7.09/1.50  --bmc1_aig_witness_out                  false
% 7.09/1.50  --bmc1_verbose                          false
% 7.09/1.50  --bmc1_dump_clauses_tptp                false
% 7.09/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.09/1.50  --bmc1_dump_file                        -
% 7.09/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.09/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.09/1.50  --bmc1_ucm_extend_mode                  1
% 7.09/1.50  --bmc1_ucm_init_mode                    2
% 7.09/1.50  --bmc1_ucm_cone_mode                    none
% 7.09/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.09/1.50  --bmc1_ucm_relax_model                  4
% 7.09/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.09/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.09/1.50  --bmc1_ucm_layered_model                none
% 7.09/1.50  --bmc1_ucm_max_lemma_size               10
% 7.09/1.50  
% 7.09/1.50  ------ AIG Options
% 7.09/1.50  
% 7.09/1.50  --aig_mode                              false
% 7.09/1.50  
% 7.09/1.50  ------ Instantiation Options
% 7.09/1.50  
% 7.09/1.50  --instantiation_flag                    true
% 7.09/1.50  --inst_sos_flag                         true
% 7.09/1.50  --inst_sos_phase                        true
% 7.09/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.09/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.09/1.50  --inst_lit_sel_side                     num_symb
% 7.09/1.50  --inst_solver_per_active                1400
% 7.09/1.50  --inst_solver_calls_frac                1.
% 7.09/1.50  --inst_passive_queue_type               priority_queues
% 7.09/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.09/1.50  --inst_passive_queues_freq              [25;2]
% 7.09/1.50  --inst_dismatching                      true
% 7.09/1.50  --inst_eager_unprocessed_to_passive     true
% 7.09/1.50  --inst_prop_sim_given                   true
% 7.09/1.50  --inst_prop_sim_new                     false
% 7.09/1.50  --inst_subs_new                         false
% 7.09/1.50  --inst_eq_res_simp                      false
% 7.09/1.50  --inst_subs_given                       false
% 7.09/1.50  --inst_orphan_elimination               true
% 7.09/1.50  --inst_learning_loop_flag               true
% 7.09/1.50  --inst_learning_start                   3000
% 7.09/1.50  --inst_learning_factor                  2
% 7.09/1.50  --inst_start_prop_sim_after_learn       3
% 7.09/1.50  --inst_sel_renew                        solver
% 7.09/1.50  --inst_lit_activity_flag                true
% 7.09/1.50  --inst_restr_to_given                   false
% 7.09/1.50  --inst_activity_threshold               500
% 7.09/1.50  --inst_out_proof                        true
% 7.09/1.50  
% 7.09/1.50  ------ Resolution Options
% 7.09/1.50  
% 7.09/1.50  --resolution_flag                       true
% 7.09/1.50  --res_lit_sel                           adaptive
% 7.09/1.50  --res_lit_sel_side                      none
% 7.09/1.50  --res_ordering                          kbo
% 7.09/1.50  --res_to_prop_solver                    active
% 7.09/1.50  --res_prop_simpl_new                    false
% 7.09/1.50  --res_prop_simpl_given                  true
% 7.09/1.50  --res_passive_queue_type                priority_queues
% 7.09/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.09/1.50  --res_passive_queues_freq               [15;5]
% 7.09/1.50  --res_forward_subs                      full
% 7.09/1.50  --res_backward_subs                     full
% 7.09/1.50  --res_forward_subs_resolution           true
% 7.09/1.50  --res_backward_subs_resolution          true
% 7.09/1.50  --res_orphan_elimination                true
% 7.09/1.50  --res_time_limit                        2.
% 7.09/1.50  --res_out_proof                         true
% 7.09/1.50  
% 7.09/1.50  ------ Superposition Options
% 7.09/1.50  
% 7.09/1.50  --superposition_flag                    true
% 7.09/1.50  --sup_passive_queue_type                priority_queues
% 7.09/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.09/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.09/1.50  --demod_completeness_check              fast
% 7.09/1.50  --demod_use_ground                      true
% 7.09/1.50  --sup_to_prop_solver                    passive
% 7.09/1.50  --sup_prop_simpl_new                    true
% 7.09/1.50  --sup_prop_simpl_given                  true
% 7.09/1.50  --sup_fun_splitting                     true
% 7.09/1.50  --sup_smt_interval                      50000
% 7.09/1.50  
% 7.09/1.50  ------ Superposition Simplification Setup
% 7.09/1.50  
% 7.09/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.09/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.09/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.09/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.09/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.09/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.09/1.50  --sup_immed_triv                        [TrivRules]
% 7.09/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.50  --sup_immed_bw_main                     []
% 7.09/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.09/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.09/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.50  --sup_input_bw                          []
% 7.09/1.50  
% 7.09/1.50  ------ Combination Options
% 7.09/1.50  
% 7.09/1.50  --comb_res_mult                         3
% 7.09/1.50  --comb_sup_mult                         2
% 7.09/1.50  --comb_inst_mult                        10
% 7.09/1.50  
% 7.09/1.50  ------ Debug Options
% 7.09/1.50  
% 7.09/1.50  --dbg_backtrace                         false
% 7.09/1.50  --dbg_dump_prop_clauses                 false
% 7.09/1.50  --dbg_dump_prop_clauses_file            -
% 7.09/1.50  --dbg_out_stat                          false
% 7.09/1.50  ------ Parsing...
% 7.09/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.09/1.50  
% 7.09/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.09/1.50  
% 7.09/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.09/1.50  
% 7.09/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.09/1.50  ------ Proving...
% 7.09/1.50  ------ Problem Properties 
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  clauses                                 30
% 7.09/1.50  conjectures                             14
% 7.09/1.50  EPR                                     10
% 7.09/1.50  Horn                                    21
% 7.09/1.50  unary                                   15
% 7.09/1.50  binary                                  3
% 7.09/1.50  lits                                    128
% 7.09/1.50  lits eq                                 16
% 7.09/1.50  fd_pure                                 0
% 7.09/1.50  fd_pseudo                               0
% 7.09/1.50  fd_cond                                 0
% 7.09/1.50  fd_pseudo_cond                          1
% 7.09/1.50  AC symbols                              0
% 7.09/1.50  
% 7.09/1.50  ------ Schedule dynamic 5 is on 
% 7.09/1.50  
% 7.09/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  ------ 
% 7.09/1.50  Current options:
% 7.09/1.50  ------ 
% 7.09/1.50  
% 7.09/1.50  ------ Input Options
% 7.09/1.50  
% 7.09/1.50  --out_options                           all
% 7.09/1.50  --tptp_safe_out                         true
% 7.09/1.50  --problem_path                          ""
% 7.09/1.50  --include_path                          ""
% 7.09/1.50  --clausifier                            res/vclausify_rel
% 7.09/1.50  --clausifier_options                    ""
% 7.09/1.50  --stdin                                 false
% 7.09/1.50  --stats_out                             all
% 7.09/1.50  
% 7.09/1.50  ------ General Options
% 7.09/1.50  
% 7.09/1.50  --fof                                   false
% 7.09/1.50  --time_out_real                         305.
% 7.09/1.50  --time_out_virtual                      -1.
% 7.09/1.50  --symbol_type_check                     false
% 7.09/1.50  --clausify_out                          false
% 7.09/1.50  --sig_cnt_out                           false
% 7.09/1.50  --trig_cnt_out                          false
% 7.09/1.50  --trig_cnt_out_tolerance                1.
% 7.09/1.50  --trig_cnt_out_sk_spl                   false
% 7.09/1.50  --abstr_cl_out                          false
% 7.09/1.50  
% 7.09/1.50  ------ Global Options
% 7.09/1.50  
% 7.09/1.50  --schedule                              default
% 7.09/1.50  --add_important_lit                     false
% 7.09/1.50  --prop_solver_per_cl                    1000
% 7.09/1.50  --min_unsat_core                        false
% 7.09/1.50  --soft_assumptions                      false
% 7.09/1.50  --soft_lemma_size                       3
% 7.09/1.50  --prop_impl_unit_size                   0
% 7.09/1.50  --prop_impl_unit                        []
% 7.09/1.50  --share_sel_clauses                     true
% 7.09/1.50  --reset_solvers                         false
% 7.09/1.50  --bc_imp_inh                            [conj_cone]
% 7.09/1.50  --conj_cone_tolerance                   3.
% 7.09/1.50  --extra_neg_conj                        none
% 7.09/1.50  --large_theory_mode                     true
% 7.09/1.50  --prolific_symb_bound                   200
% 7.09/1.50  --lt_threshold                          2000
% 7.09/1.50  --clause_weak_htbl                      true
% 7.09/1.50  --gc_record_bc_elim                     false
% 7.09/1.50  
% 7.09/1.50  ------ Preprocessing Options
% 7.09/1.50  
% 7.09/1.50  --preprocessing_flag                    true
% 7.09/1.50  --time_out_prep_mult                    0.1
% 7.09/1.50  --splitting_mode                        input
% 7.09/1.50  --splitting_grd                         true
% 7.09/1.50  --splitting_cvd                         false
% 7.09/1.50  --splitting_cvd_svl                     false
% 7.09/1.50  --splitting_nvd                         32
% 7.09/1.50  --sub_typing                            true
% 7.09/1.50  --prep_gs_sim                           true
% 7.09/1.50  --prep_unflatten                        true
% 7.09/1.50  --prep_res_sim                          true
% 7.09/1.50  --prep_upred                            true
% 7.09/1.50  --prep_sem_filter                       exhaustive
% 7.09/1.50  --prep_sem_filter_out                   false
% 7.09/1.50  --pred_elim                             true
% 7.09/1.50  --res_sim_input                         true
% 7.09/1.50  --eq_ax_congr_red                       true
% 7.09/1.50  --pure_diseq_elim                       true
% 7.09/1.50  --brand_transform                       false
% 7.09/1.50  --non_eq_to_eq                          false
% 7.09/1.50  --prep_def_merge                        true
% 7.09/1.50  --prep_def_merge_prop_impl              false
% 7.09/1.50  --prep_def_merge_mbd                    true
% 7.09/1.50  --prep_def_merge_tr_red                 false
% 7.09/1.50  --prep_def_merge_tr_cl                  false
% 7.09/1.50  --smt_preprocessing                     true
% 7.09/1.50  --smt_ac_axioms                         fast
% 7.09/1.50  --preprocessed_out                      false
% 7.09/1.50  --preprocessed_stats                    false
% 7.09/1.50  
% 7.09/1.50  ------ Abstraction refinement Options
% 7.09/1.50  
% 7.09/1.50  --abstr_ref                             []
% 7.09/1.50  --abstr_ref_prep                        false
% 7.09/1.50  --abstr_ref_until_sat                   false
% 7.09/1.50  --abstr_ref_sig_restrict                funpre
% 7.09/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.09/1.50  --abstr_ref_under                       []
% 7.09/1.50  
% 7.09/1.50  ------ SAT Options
% 7.09/1.50  
% 7.09/1.50  --sat_mode                              false
% 7.09/1.50  --sat_fm_restart_options                ""
% 7.09/1.50  --sat_gr_def                            false
% 7.09/1.50  --sat_epr_types                         true
% 7.09/1.50  --sat_non_cyclic_types                  false
% 7.09/1.50  --sat_finite_models                     false
% 7.09/1.50  --sat_fm_lemmas                         false
% 7.09/1.50  --sat_fm_prep                           false
% 7.09/1.50  --sat_fm_uc_incr                        true
% 7.09/1.50  --sat_out_model                         small
% 7.09/1.50  --sat_out_clauses                       false
% 7.09/1.50  
% 7.09/1.50  ------ QBF Options
% 7.09/1.50  
% 7.09/1.50  --qbf_mode                              false
% 7.09/1.50  --qbf_elim_univ                         false
% 7.09/1.50  --qbf_dom_inst                          none
% 7.09/1.50  --qbf_dom_pre_inst                      false
% 7.09/1.50  --qbf_sk_in                             false
% 7.09/1.50  --qbf_pred_elim                         true
% 7.09/1.50  --qbf_split                             512
% 7.09/1.50  
% 7.09/1.50  ------ BMC1 Options
% 7.09/1.50  
% 7.09/1.50  --bmc1_incremental                      false
% 7.09/1.50  --bmc1_axioms                           reachable_all
% 7.09/1.50  --bmc1_min_bound                        0
% 7.09/1.50  --bmc1_max_bound                        -1
% 7.09/1.50  --bmc1_max_bound_default                -1
% 7.09/1.50  --bmc1_symbol_reachability              true
% 7.09/1.50  --bmc1_property_lemmas                  false
% 7.09/1.50  --bmc1_k_induction                      false
% 7.09/1.50  --bmc1_non_equiv_states                 false
% 7.09/1.50  --bmc1_deadlock                         false
% 7.09/1.50  --bmc1_ucm                              false
% 7.09/1.50  --bmc1_add_unsat_core                   none
% 7.09/1.50  --bmc1_unsat_core_children              false
% 7.09/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.09/1.50  --bmc1_out_stat                         full
% 7.09/1.50  --bmc1_ground_init                      false
% 7.09/1.50  --bmc1_pre_inst_next_state              false
% 7.09/1.50  --bmc1_pre_inst_state                   false
% 7.09/1.50  --bmc1_pre_inst_reach_state             false
% 7.09/1.50  --bmc1_out_unsat_core                   false
% 7.09/1.50  --bmc1_aig_witness_out                  false
% 7.09/1.50  --bmc1_verbose                          false
% 7.09/1.50  --bmc1_dump_clauses_tptp                false
% 7.09/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.09/1.50  --bmc1_dump_file                        -
% 7.09/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.09/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.09/1.50  --bmc1_ucm_extend_mode                  1
% 7.09/1.50  --bmc1_ucm_init_mode                    2
% 7.09/1.50  --bmc1_ucm_cone_mode                    none
% 7.09/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.09/1.50  --bmc1_ucm_relax_model                  4
% 7.09/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.09/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.09/1.50  --bmc1_ucm_layered_model                none
% 7.09/1.50  --bmc1_ucm_max_lemma_size               10
% 7.09/1.50  
% 7.09/1.50  ------ AIG Options
% 7.09/1.50  
% 7.09/1.50  --aig_mode                              false
% 7.09/1.50  
% 7.09/1.50  ------ Instantiation Options
% 7.09/1.50  
% 7.09/1.50  --instantiation_flag                    true
% 7.09/1.50  --inst_sos_flag                         true
% 7.09/1.50  --inst_sos_phase                        true
% 7.09/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.09/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.09/1.50  --inst_lit_sel_side                     none
% 7.09/1.50  --inst_solver_per_active                1400
% 7.09/1.50  --inst_solver_calls_frac                1.
% 7.09/1.50  --inst_passive_queue_type               priority_queues
% 7.09/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.09/1.50  --inst_passive_queues_freq              [25;2]
% 7.09/1.50  --inst_dismatching                      true
% 7.09/1.50  --inst_eager_unprocessed_to_passive     true
% 7.09/1.50  --inst_prop_sim_given                   true
% 7.09/1.50  --inst_prop_sim_new                     false
% 7.09/1.50  --inst_subs_new                         false
% 7.09/1.50  --inst_eq_res_simp                      false
% 7.09/1.50  --inst_subs_given                       false
% 7.09/1.50  --inst_orphan_elimination               true
% 7.09/1.50  --inst_learning_loop_flag               true
% 7.09/1.50  --inst_learning_start                   3000
% 7.09/1.50  --inst_learning_factor                  2
% 7.09/1.50  --inst_start_prop_sim_after_learn       3
% 7.09/1.50  --inst_sel_renew                        solver
% 7.09/1.50  --inst_lit_activity_flag                true
% 7.09/1.50  --inst_restr_to_given                   false
% 7.09/1.50  --inst_activity_threshold               500
% 7.09/1.50  --inst_out_proof                        true
% 7.09/1.50  
% 7.09/1.50  ------ Resolution Options
% 7.09/1.50  
% 7.09/1.50  --resolution_flag                       false
% 7.09/1.50  --res_lit_sel                           adaptive
% 7.09/1.50  --res_lit_sel_side                      none
% 7.09/1.50  --res_ordering                          kbo
% 7.09/1.50  --res_to_prop_solver                    active
% 7.09/1.50  --res_prop_simpl_new                    false
% 7.09/1.50  --res_prop_simpl_given                  true
% 7.09/1.50  --res_passive_queue_type                priority_queues
% 7.09/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.09/1.50  --res_passive_queues_freq               [15;5]
% 7.09/1.50  --res_forward_subs                      full
% 7.09/1.50  --res_backward_subs                     full
% 7.09/1.50  --res_forward_subs_resolution           true
% 7.09/1.50  --res_backward_subs_resolution          true
% 7.09/1.50  --res_orphan_elimination                true
% 7.09/1.50  --res_time_limit                        2.
% 7.09/1.50  --res_out_proof                         true
% 7.09/1.50  
% 7.09/1.50  ------ Superposition Options
% 7.09/1.50  
% 7.09/1.50  --superposition_flag                    true
% 7.09/1.50  --sup_passive_queue_type                priority_queues
% 7.09/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.09/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.09/1.50  --demod_completeness_check              fast
% 7.09/1.50  --demod_use_ground                      true
% 7.09/1.50  --sup_to_prop_solver                    passive
% 7.09/1.50  --sup_prop_simpl_new                    true
% 7.09/1.50  --sup_prop_simpl_given                  true
% 7.09/1.50  --sup_fun_splitting                     true
% 7.09/1.50  --sup_smt_interval                      50000
% 7.09/1.50  
% 7.09/1.50  ------ Superposition Simplification Setup
% 7.09/1.50  
% 7.09/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.09/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.09/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.09/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.09/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.09/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.09/1.50  --sup_immed_triv                        [TrivRules]
% 7.09/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.50  --sup_immed_bw_main                     []
% 7.09/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.09/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.09/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.50  --sup_input_bw                          []
% 7.09/1.50  
% 7.09/1.50  ------ Combination Options
% 7.09/1.50  
% 7.09/1.50  --comb_res_mult                         3
% 7.09/1.50  --comb_sup_mult                         2
% 7.09/1.50  --comb_inst_mult                        10
% 7.09/1.50  
% 7.09/1.50  ------ Debug Options
% 7.09/1.50  
% 7.09/1.50  --dbg_backtrace                         false
% 7.09/1.50  --dbg_dump_prop_clauses                 false
% 7.09/1.50  --dbg_dump_prop_clauses_file            -
% 7.09/1.50  --dbg_out_stat                          false
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  ------ Proving...
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  % SZS status Theorem for theBenchmark.p
% 7.09/1.50  
% 7.09/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.09/1.50  
% 7.09/1.50  fof(f16,conjecture,(
% 7.09/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f17,negated_conjecture,(
% 7.09/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.09/1.50    inference(negated_conjecture,[],[f16])).
% 7.09/1.50  
% 7.09/1.50  fof(f39,plain,(
% 7.09/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.09/1.50    inference(ennf_transformation,[],[f17])).
% 7.09/1.50  
% 7.09/1.50  fof(f40,plain,(
% 7.09/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.09/1.50    inference(flattening,[],[f39])).
% 7.09/1.50  
% 7.09/1.50  fof(f50,plain,(
% 7.09/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.09/1.50    introduced(choice_axiom,[])).
% 7.09/1.50  
% 7.09/1.50  fof(f49,plain,(
% 7.09/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.09/1.50    introduced(choice_axiom,[])).
% 7.09/1.50  
% 7.09/1.50  fof(f48,plain,(
% 7.09/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.09/1.50    introduced(choice_axiom,[])).
% 7.09/1.50  
% 7.09/1.50  fof(f47,plain,(
% 7.09/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.09/1.50    introduced(choice_axiom,[])).
% 7.09/1.50  
% 7.09/1.50  fof(f46,plain,(
% 7.09/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.09/1.50    introduced(choice_axiom,[])).
% 7.09/1.50  
% 7.09/1.50  fof(f45,plain,(
% 7.09/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.09/1.50    introduced(choice_axiom,[])).
% 7.09/1.50  
% 7.09/1.50  fof(f51,plain,(
% 7.09/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.09/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f50,f49,f48,f47,f46,f45])).
% 7.09/1.50  
% 7.09/1.50  fof(f79,plain,(
% 7.09/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f3,axiom,(
% 7.09/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f19,plain,(
% 7.09/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.09/1.50    inference(ennf_transformation,[],[f3])).
% 7.09/1.50  
% 7.09/1.50  fof(f54,plain,(
% 7.09/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.09/1.50    inference(cnf_transformation,[],[f19])).
% 7.09/1.50  
% 7.09/1.50  fof(f83,plain,(
% 7.09/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f13,axiom,(
% 7.09/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f33,plain,(
% 7.09/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.09/1.50    inference(ennf_transformation,[],[f13])).
% 7.09/1.50  
% 7.09/1.50  fof(f34,plain,(
% 7.09/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.09/1.50    inference(flattening,[],[f33])).
% 7.09/1.50  
% 7.09/1.50  fof(f67,plain,(
% 7.09/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f34])).
% 7.09/1.50  
% 7.09/1.50  fof(f81,plain,(
% 7.09/1.50    v1_funct_1(sK4)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f86,plain,(
% 7.09/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f84,plain,(
% 7.09/1.50    v1_funct_1(sK5)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f14,axiom,(
% 7.09/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f35,plain,(
% 7.09/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.50    inference(ennf_transformation,[],[f14])).
% 7.09/1.50  
% 7.09/1.50  fof(f36,plain,(
% 7.09/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.50    inference(flattening,[],[f35])).
% 7.09/1.50  
% 7.09/1.50  fof(f43,plain,(
% 7.09/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.50    inference(nnf_transformation,[],[f36])).
% 7.09/1.50  
% 7.09/1.50  fof(f44,plain,(
% 7.09/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.50    inference(flattening,[],[f43])).
% 7.09/1.50  
% 7.09/1.50  fof(f69,plain,(
% 7.09/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f44])).
% 7.09/1.50  
% 7.09/1.50  fof(f91,plain,(
% 7.09/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(equality_resolution,[],[f69])).
% 7.09/1.50  
% 7.09/1.50  fof(f15,axiom,(
% 7.09/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f37,plain,(
% 7.09/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.09/1.50    inference(ennf_transformation,[],[f15])).
% 7.09/1.50  
% 7.09/1.50  fof(f38,plain,(
% 7.09/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.50    inference(flattening,[],[f37])).
% 7.09/1.50  
% 7.09/1.50  fof(f71,plain,(
% 7.09/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f38])).
% 7.09/1.50  
% 7.09/1.50  fof(f72,plain,(
% 7.09/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f38])).
% 7.09/1.50  
% 7.09/1.50  fof(f73,plain,(
% 7.09/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f38])).
% 7.09/1.50  
% 7.09/1.50  fof(f75,plain,(
% 7.09/1.50    ~v1_xboole_0(sK1)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f78,plain,(
% 7.09/1.50    ~v1_xboole_0(sK3)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f85,plain,(
% 7.09/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f76,plain,(
% 7.09/1.50    ~v1_xboole_0(sK2)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f82,plain,(
% 7.09/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f4,axiom,(
% 7.09/1.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f20,plain,(
% 7.09/1.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.09/1.50    inference(ennf_transformation,[],[f4])).
% 7.09/1.50  
% 7.09/1.50  fof(f55,plain,(
% 7.09/1.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f20])).
% 7.09/1.50  
% 7.09/1.50  fof(f80,plain,(
% 7.09/1.50    r1_subset_1(sK2,sK3)),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f8,axiom,(
% 7.09/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f25,plain,(
% 7.09/1.50    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.09/1.50    inference(ennf_transformation,[],[f8])).
% 7.09/1.50  
% 7.09/1.50  fof(f26,plain,(
% 7.09/1.50    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.50    inference(flattening,[],[f25])).
% 7.09/1.50  
% 7.09/1.50  fof(f60,plain,(
% 7.09/1.50    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f26])).
% 7.09/1.50  
% 7.09/1.50  fof(f11,axiom,(
% 7.09/1.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f29,plain,(
% 7.09/1.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.09/1.50    inference(ennf_transformation,[],[f11])).
% 7.09/1.50  
% 7.09/1.50  fof(f30,plain,(
% 7.09/1.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.09/1.50    inference(flattening,[],[f29])).
% 7.09/1.50  
% 7.09/1.50  fof(f64,plain,(
% 7.09/1.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f30])).
% 7.09/1.50  
% 7.09/1.50  fof(f10,axiom,(
% 7.09/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f18,plain,(
% 7.09/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.09/1.50    inference(pure_predicate_removal,[],[f10])).
% 7.09/1.50  
% 7.09/1.50  fof(f28,plain,(
% 7.09/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.09/1.50    inference(ennf_transformation,[],[f18])).
% 7.09/1.50  
% 7.09/1.50  fof(f62,plain,(
% 7.09/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.09/1.50    inference(cnf_transformation,[],[f28])).
% 7.09/1.50  
% 7.09/1.50  fof(f12,axiom,(
% 7.09/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f31,plain,(
% 7.09/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.09/1.50    inference(ennf_transformation,[],[f12])).
% 7.09/1.50  
% 7.09/1.50  fof(f32,plain,(
% 7.09/1.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.09/1.50    inference(flattening,[],[f31])).
% 7.09/1.50  
% 7.09/1.50  fof(f42,plain,(
% 7.09/1.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.09/1.50    inference(nnf_transformation,[],[f32])).
% 7.09/1.50  
% 7.09/1.50  fof(f65,plain,(
% 7.09/1.50    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f42])).
% 7.09/1.50  
% 7.09/1.50  fof(f9,axiom,(
% 7.09/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f27,plain,(
% 7.09/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.09/1.50    inference(ennf_transformation,[],[f9])).
% 7.09/1.50  
% 7.09/1.50  fof(f61,plain,(
% 7.09/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.09/1.50    inference(cnf_transformation,[],[f27])).
% 7.09/1.50  
% 7.09/1.50  fof(f6,axiom,(
% 7.09/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f22,plain,(
% 7.09/1.50    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.09/1.50    inference(ennf_transformation,[],[f6])).
% 7.09/1.50  
% 7.09/1.50  fof(f57,plain,(
% 7.09/1.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f22])).
% 7.09/1.50  
% 7.09/1.50  fof(f7,axiom,(
% 7.09/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f23,plain,(
% 7.09/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.09/1.50    inference(ennf_transformation,[],[f7])).
% 7.09/1.50  
% 7.09/1.50  fof(f24,plain,(
% 7.09/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.50    inference(flattening,[],[f23])).
% 7.09/1.50  
% 7.09/1.50  fof(f41,plain,(
% 7.09/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.50    inference(nnf_transformation,[],[f24])).
% 7.09/1.50  
% 7.09/1.50  fof(f58,plain,(
% 7.09/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f41])).
% 7.09/1.50  
% 7.09/1.50  fof(f5,axiom,(
% 7.09/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f21,plain,(
% 7.09/1.50    ! [X0,X1,X2] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.09/1.50    inference(ennf_transformation,[],[f5])).
% 7.09/1.50  
% 7.09/1.50  fof(f56,plain,(
% 7.09/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f21])).
% 7.09/1.50  
% 7.09/1.50  fof(f2,axiom,(
% 7.09/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f53,plain,(
% 7.09/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.09/1.50    inference(cnf_transformation,[],[f2])).
% 7.09/1.50  
% 7.09/1.50  fof(f1,axiom,(
% 7.09/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.09/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.09/1.50  
% 7.09/1.50  fof(f52,plain,(
% 7.09/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f1])).
% 7.09/1.50  
% 7.09/1.50  fof(f68,plain,(
% 7.09/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(cnf_transformation,[],[f44])).
% 7.09/1.50  
% 7.09/1.50  fof(f92,plain,(
% 7.09/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.50    inference(equality_resolution,[],[f68])).
% 7.09/1.50  
% 7.09/1.50  fof(f77,plain,(
% 7.09/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  fof(f87,plain,(
% 7.09/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.09/1.50    inference(cnf_transformation,[],[f51])).
% 7.09/1.50  
% 7.09/1.50  cnf(c_30,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.09/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_759,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_30]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1276,plain,
% 7.09/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.09/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.09/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_777,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.09/1.50      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1259,plain,
% 7.09/1.50      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.09/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_777]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2135,plain,
% 7.09/1.50      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1276,c_1259]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_26,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.09/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_763,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_26]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1272,plain,
% 7.09/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_15,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.09/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_772,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.50      | ~ v1_funct_1(X0_53)
% 7.09/1.50      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_15]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1264,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.09/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.50      | v1_funct_1(X2_53) != iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2592,plain,
% 7.09/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.09/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1272,c_1264]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_28,negated_conjecture,
% 7.09/1.50      ( v1_funct_1(sK4) ),
% 7.09/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_43,plain,
% 7.09/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2886,plain,
% 7.09/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_2592,c_43]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_23,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.09/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_766,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_23]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1269,plain,
% 7.09/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2591,plain,
% 7.09/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.09/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1269,c_1264]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_25,negated_conjecture,
% 7.09/1.50      ( v1_funct_1(sK5) ),
% 7.09/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_46,plain,
% 7.09/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2881,plain,
% 7.09/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_2591,c_46]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_17,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.09/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_21,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_20,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_19,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_193,plain,
% 7.09/1.50      ( ~ v1_funct_1(X3)
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_17,c_21,c_20,c_19]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_194,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_193]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_752,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.09/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.09/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.09/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.09/1.50      | ~ v1_funct_1(X0_53)
% 7.09/1.50      | ~ v1_funct_1(X3_53)
% 7.09/1.50      | v1_xboole_0(X2_53)
% 7.09/1.50      | v1_xboole_0(X1_53)
% 7.09/1.50      | v1_xboole_0(X4_53)
% 7.09/1.50      | v1_xboole_0(X5_53)
% 7.09/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_194]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1283,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.09/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.09/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.09/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.09/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3820,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 7.09/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.50      | v1_funct_1(sK5) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2881,c_1283]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_34,negated_conjecture,
% 7.09/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_37,plain,
% 7.09/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_31,negated_conjecture,
% 7.09/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.09/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_40,plain,
% 7.09/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_24,negated_conjecture,
% 7.09/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_47,plain,
% 7.09/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_48,plain,
% 7.09/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7055,plain,
% 7.09/1.50      ( v1_funct_1(X1_53) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 7.09/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_3820,c_37,c_40,c_46,c_47,c_48]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7056,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 7.09/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_7055]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7062,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.09/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.09/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | v1_funct_1(sK4) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2886,c_7056]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_33,negated_conjecture,
% 7.09/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.09/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_38,plain,
% 7.09/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_27,negated_conjecture,
% 7.09/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_44,plain,
% 7.09/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_45,plain,
% 7.09/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.09/1.50      | ~ v1_xboole_0(X1)
% 7.09/1.50      | v1_xboole_0(X0) ),
% 7.09/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_776,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.09/1.50      | ~ v1_xboole_0(X1_53)
% 7.09/1.50      | v1_xboole_0(X0_53) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1448,plain,
% 7.09/1.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_53))
% 7.09/1.50      | ~ v1_xboole_0(X0_53)
% 7.09/1.50      | v1_xboole_0(sK2) ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_776]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1449,plain,
% 7.09/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_1448]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7072,plain,
% 7.09/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_7062,c_38,c_43,c_44,c_45,c_1449]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7073,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_7072]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7078,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2135,c_7073]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_29,negated_conjecture,
% 7.09/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.09/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_760,negated_conjecture,
% 7.09/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_29]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1275,plain,
% 7.09/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_8,plain,
% 7.09/1.50      ( ~ r1_subset_1(X0,X1)
% 7.09/1.50      | r1_subset_1(X1,X0)
% 7.09/1.50      | v1_xboole_0(X0)
% 7.09/1.50      | v1_xboole_0(X1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_774,plain,
% 7.09/1.50      ( ~ r1_subset_1(X0_53,X1_53)
% 7.09/1.50      | r1_subset_1(X1_53,X0_53)
% 7.09/1.50      | v1_xboole_0(X0_53)
% 7.09/1.50      | v1_xboole_0(X1_53) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1262,plain,
% 7.09/1.50      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 7.09/1.50      | r1_subset_1(X1_53,X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2588,plain,
% 7.09/1.50      ( r1_subset_1(sK3,sK2) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1275,c_1262]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_42,plain,
% 7.09/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1447,plain,
% 7.09/1.50      ( r1_subset_1(X0_53,sK2)
% 7.09/1.50      | ~ r1_subset_1(sK2,X0_53)
% 7.09/1.50      | v1_xboole_0(X0_53)
% 7.09/1.50      | v1_xboole_0(sK2) ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_774]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1630,plain,
% 7.09/1.50      ( r1_subset_1(sK3,sK2)
% 7.09/1.50      | ~ r1_subset_1(sK2,sK3)
% 7.09/1.50      | v1_xboole_0(sK3)
% 7.09/1.50      | v1_xboole_0(sK2) ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_1447]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1631,plain,
% 7.09/1.50      ( r1_subset_1(sK3,sK2) = iProver_top
% 7.09/1.50      | r1_subset_1(sK2,sK3) != iProver_top
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_1630]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3117,plain,
% 7.09/1.50      ( r1_subset_1(sK3,sK2) = iProver_top ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_2588,c_38,c_40,c_42,c_1631]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_11,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | v1_partfun1(X0,X1)
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | v1_xboole_0(X2) ),
% 7.09/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_10,plain,
% 7.09/1.50      ( v4_relat_1(X0,X1)
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.09/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_14,plain,
% 7.09/1.50      ( ~ v1_partfun1(X0,X1)
% 7.09/1.50      | ~ v4_relat_1(X0,X1)
% 7.09/1.50      | ~ v1_relat_1(X0)
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_362,plain,
% 7.09/1.50      ( ~ v1_partfun1(X0,X1)
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ v1_relat_1(X0)
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(resolution,[status(thm)],[c_10,c_14]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_9,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | v1_relat_1(X0) ),
% 7.09/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_366,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ v1_partfun1(X0,X1)
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_362,c_14,c_10,c_9]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_367,plain,
% 7.09/1.50      ( ~ v1_partfun1(X0,X1)
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_366]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_437,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(resolution,[status(thm)],[c_11,c_367]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_441,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_437,c_14,c_11,c_10,c_9]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_442,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | k1_relat_1(X0) = X1 ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_441]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_751,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.50      | ~ v1_funct_1(X0_53)
% 7.09/1.50      | v1_xboole_0(X2_53)
% 7.09/1.50      | k1_relat_1(X0_53) = X1_53 ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_442]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1284,plain,
% 7.09/1.50      ( k1_relat_1(X0_53) = X1_53
% 7.09/1.50      | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.09/1.50      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_4694,plain,
% 7.09/1.50      ( k1_relat_1(sK4) = sK2
% 7.09/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.09/1.50      | v1_funct_1(sK4) != iProver_top
% 7.09/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1272,c_1284]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1394,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0_53,X1_53,sK1)
% 7.09/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1)))
% 7.09/1.50      | ~ v1_funct_1(X0_53)
% 7.09/1.50      | v1_xboole_0(sK1)
% 7.09/1.50      | k1_relat_1(X0_53) = X1_53 ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_751]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1664,plain,
% 7.09/1.50      ( ~ v1_funct_2(sK4,X0_53,sK1)
% 7.09/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
% 7.09/1.50      | ~ v1_funct_1(sK4)
% 7.09/1.50      | v1_xboole_0(sK1)
% 7.09/1.50      | k1_relat_1(sK4) = X0_53 ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_1394]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1666,plain,
% 7.09/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.09/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.09/1.50      | ~ v1_funct_1(sK4)
% 7.09/1.50      | v1_xboole_0(sK1)
% 7.09/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_1664]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_4805,plain,
% 7.09/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_4694,c_34,c_28,c_27,c_26,c_1666]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_5,plain,
% 7.09/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.09/1.50      | ~ v1_relat_1(X1)
% 7.09/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.09/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7,plain,
% 7.09/1.50      ( ~ r1_subset_1(X0,X1)
% 7.09/1.50      | r1_xboole_0(X0,X1)
% 7.09/1.50      | v1_xboole_0(X0)
% 7.09/1.50      | v1_xboole_0(X1) ),
% 7.09/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_470,plain,
% 7.09/1.50      ( ~ r1_subset_1(X0,X1)
% 7.09/1.50      | ~ v1_relat_1(X2)
% 7.09/1.50      | v1_xboole_0(X0)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | X0 != X3
% 7.09/1.50      | k7_relat_1(X2,X3) = k1_xboole_0
% 7.09/1.50      | k1_relat_1(X2) != X1 ),
% 7.09/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_471,plain,
% 7.09/1.50      ( ~ r1_subset_1(X0,k1_relat_1(X1))
% 7.09/1.50      | ~ v1_relat_1(X1)
% 7.09/1.50      | v1_xboole_0(X0)
% 7.09/1.50      | v1_xboole_0(k1_relat_1(X1))
% 7.09/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.09/1.50      inference(unflattening,[status(thm)],[c_470]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_750,plain,
% 7.09/1.50      ( ~ r1_subset_1(X0_53,k1_relat_1(X1_53))
% 7.09/1.50      | ~ v1_relat_1(X1_53)
% 7.09/1.50      | v1_xboole_0(X0_53)
% 7.09/1.50      | v1_xboole_0(k1_relat_1(X1_53))
% 7.09/1.50      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_471]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1285,plain,
% 7.09/1.50      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X1_53,k1_relat_1(X0_53)) != iProver_top
% 7.09/1.50      | v1_relat_1(X0_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(k1_relat_1(X0_53)) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_5026,plain,
% 7.09/1.50      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK2) != iProver_top
% 7.09/1.50      | v1_relat_1(sK4) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_4805,c_1285]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_5027,plain,
% 7.09/1.50      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK2) != iProver_top
% 7.09/1.50      | v1_relat_1(sK4) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(light_normalisation,[status(thm)],[c_5026,c_4805]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_773,plain,
% 7.09/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.50      | v1_relat_1(X0_53) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1825,plain,
% 7.09/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.09/1.50      | v1_relat_1(sK4) ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_773]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1826,plain,
% 7.09/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.09/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_1825]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6470,plain,
% 7.09/1.50      ( v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK2) != iProver_top ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_5027,c_38,c_45,c_1826]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6471,plain,
% 7.09/1.50      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK2) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_6470]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6476,plain,
% 7.09/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_3117,c_6471]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6508,plain,
% 7.09/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_6476,c_40]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1263,plain,
% 7.09/1.50      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.09/1.50      | v1_relat_1(X0_53) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2499,plain,
% 7.09/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1272,c_1263]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_4,plain,
% 7.09/1.50      ( ~ v1_relat_1(X0)
% 7.09/1.50      | k3_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.09/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_775,plain,
% 7.09/1.50      ( ~ v1_relat_1(X0_53)
% 7.09/1.50      | k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1261,plain,
% 7.09/1.50      ( k3_xboole_0(k7_relat_1(X0_53,X1_53),k7_relat_1(X0_53,X2_53)) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
% 7.09/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2659,plain,
% 7.09/1.50      ( k3_xboole_0(k7_relat_1(sK4,X0_53),k7_relat_1(sK4,X1_53)) = k7_relat_1(sK4,k3_xboole_0(X0_53,X1_53)) ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2499,c_1261]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6513,plain,
% 7.09/1.50      ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k3_xboole_0(k7_relat_1(sK4,X0_53),k1_xboole_0) ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_6508,c_2659]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1,plain,
% 7.09/1.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_778,plain,
% 7.09/1.50      ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6514,plain,
% 7.09/1.50      ( k7_relat_1(sK4,k3_xboole_0(X0_53,sK3)) = k1_xboole_0 ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_6513,c_778]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_4693,plain,
% 7.09/1.50      ( k1_relat_1(sK5) = sK3
% 7.09/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.50      | v1_funct_1(sK5) != iProver_top
% 7.09/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1269,c_1284]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1659,plain,
% 7.09/1.50      ( ~ v1_funct_2(sK5,X0_53,sK1)
% 7.09/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
% 7.09/1.50      | ~ v1_funct_1(sK5)
% 7.09/1.50      | v1_xboole_0(sK1)
% 7.09/1.50      | k1_relat_1(sK5) = X0_53 ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_1394]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2096,plain,
% 7.09/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.09/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.09/1.50      | ~ v1_funct_1(sK5)
% 7.09/1.50      | v1_xboole_0(sK1)
% 7.09/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_1659]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_4774,plain,
% 7.09/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_4693,c_34,c_25,c_24,c_23,c_2096]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_5025,plain,
% 7.09/1.50      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK3) != iProver_top
% 7.09/1.50      | v1_relat_1(sK5) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(k1_relat_1(sK5)) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_4774,c_1285]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_5028,plain,
% 7.09/1.50      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK3) != iProver_top
% 7.09/1.50      | v1_relat_1(sK5) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.50      inference(light_normalisation,[status(thm)],[c_5025,c_4774]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1822,plain,
% 7.09/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.09/1.50      | v1_relat_1(sK5) ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_773]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1823,plain,
% 7.09/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_1822]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6521,plain,
% 7.09/1.50      ( v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK3) != iProver_top ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_5028,c_40,c_48,c_1823]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6522,plain,
% 7.09/1.50      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(X0_53,sK3) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_6521]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6527,plain,
% 7.09/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1275,c_6522]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_5033,plain,
% 7.09/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 7.09/1.50      | r1_subset_1(sK2,sK3) != iProver_top
% 7.09/1.50      | v1_relat_1(sK5) != iProver_top
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(instantiation,[status(thm)],[c_5028]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6588,plain,
% 7.09/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_6527,c_38,c_40,c_42,c_48,c_1823,c_5033]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_0,plain,
% 7.09/1.50      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.09/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_779,plain,
% 7.09/1.50      ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2498,plain,
% 7.09/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_1269,c_1263]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2656,plain,
% 7.09/1.50      ( k3_xboole_0(k7_relat_1(sK5,X0_53),k7_relat_1(sK5,X1_53)) = k7_relat_1(sK5,k3_xboole_0(X0_53,X1_53)) ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2498,c_1261]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3101,plain,
% 7.09/1.50      ( k3_xboole_0(k7_relat_1(sK5,X0_53),k7_relat_1(sK5,X1_53)) = k7_relat_1(sK5,k3_xboole_0(X1_53,X0_53)) ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_779,c_2656]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6592,plain,
% 7.09/1.50      ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k3_xboole_0(k7_relat_1(sK5,X0_53),k1_xboole_0) ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_6588,c_3101]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6595,plain,
% 7.09/1.50      ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k1_xboole_0 ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_6592,c_778]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7079,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.50      | k1_xboole_0 != k1_xboole_0
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_7078,c_2135,c_6514,c_6595]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_7080,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.09/1.50      inference(equality_resolution_simp,[status(thm)],[c_7079]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_18,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.09/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_186,plain,
% 7.09/1.50      ( ~ v1_funct_1(X3)
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_18,c_21,c_20,c_19]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_187,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.50      | ~ v1_funct_1(X0)
% 7.09/1.50      | ~ v1_funct_1(X3)
% 7.09/1.50      | v1_xboole_0(X1)
% 7.09/1.50      | v1_xboole_0(X2)
% 7.09/1.50      | v1_xboole_0(X4)
% 7.09/1.50      | v1_xboole_0(X5)
% 7.09/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_186]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_753,plain,
% 7.09/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.09/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.09/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.09/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.09/1.50      | ~ v1_funct_1(X0_53)
% 7.09/1.50      | ~ v1_funct_1(X3_53)
% 7.09/1.50      | v1_xboole_0(X2_53)
% 7.09/1.50      | v1_xboole_0(X1_53)
% 7.09/1.50      | v1_xboole_0(X4_53)
% 7.09/1.50      | v1_xboole_0(X5_53)
% 7.09/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_187]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_1282,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.09/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.09/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.09/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.09/1.50      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.50      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(X3_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3320,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.09/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.50      | v1_funct_1(sK5) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2881,c_1282]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3546,plain,
% 7.09/1.50      ( v1_funct_1(X1_53) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.09/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_3320,c_37,c_40,c_46,c_47,c_48]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3547,plain,
% 7.09/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.09/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.50      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.50      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_3546]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3553,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.09/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.09/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | v1_funct_1(sK4) != iProver_top
% 7.09/1.50      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2886,c_3547]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3586,plain,
% 7.09/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.09/1.50      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_3553,c_38,c_43,c_44,c_45,c_1449]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3587,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.09/1.50      inference(renaming,[status(thm)],[c_3586]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3592,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.09/1.50      inference(superposition,[status(thm)],[c_2135,c_3587]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3593,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.09/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_3592,c_2135]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_32,negated_conjecture,
% 7.09/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.09/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3594,plain,
% 7.09/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 7.09/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.09/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_3593]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3656,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.09/1.50      inference(global_propositional_subsumption,
% 7.09/1.50                [status(thm)],
% 7.09/1.50                [c_3593,c_32,c_30,c_3594]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6928,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_6514,c_3656]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6932,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_6928,c_6595]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6933,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.09/1.50      inference(equality_resolution_simp,[status(thm)],[c_6932]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_22,negated_conjecture,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.09/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_767,negated_conjecture,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.09/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2309,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_2135,c_767]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_2884,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_2881,c_2309]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_3105,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_2884,c_2886]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6929,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k1_xboole_0 ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_6514,c_3105]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6930,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.09/1.50      inference(demodulation,[status(thm)],[c_6929,c_6595]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_6931,plain,
% 7.09/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.09/1.50      inference(equality_resolution_simp,[status(thm)],[c_6930]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_41,plain,
% 7.09/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(c_39,plain,
% 7.09/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.09/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.09/1.50  
% 7.09/1.50  cnf(contradiction,plain,
% 7.09/1.50      ( $false ),
% 7.09/1.50      inference(minisat,[status(thm)],[c_7080,c_6933,c_6931,c_41,c_39]) ).
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.09/1.50  
% 7.09/1.50  ------                               Statistics
% 7.09/1.50  
% 7.09/1.50  ------ General
% 7.09/1.50  
% 7.09/1.50  abstr_ref_over_cycles:                  0
% 7.09/1.50  abstr_ref_under_cycles:                 0
% 7.09/1.50  gc_basic_clause_elim:                   0
% 7.09/1.50  forced_gc_time:                         0
% 7.09/1.50  parsing_time:                           0.012
% 7.09/1.50  unif_index_cands_time:                  0.
% 7.09/1.50  unif_index_add_time:                    0.
% 7.09/1.50  orderings_time:                         0.
% 7.09/1.50  out_proof_time:                         0.023
% 7.09/1.50  total_time:                             0.511
% 7.09/1.50  num_of_symbols:                         58
% 7.09/1.50  num_of_terms:                           20349
% 7.09/1.50  
% 7.09/1.50  ------ Preprocessing
% 7.09/1.50  
% 7.09/1.50  num_of_splits:                          0
% 7.09/1.50  num_of_split_atoms:                     0
% 7.09/1.50  num_of_reused_defs:                     0
% 7.09/1.50  num_eq_ax_congr_red:                    12
% 7.09/1.50  num_of_sem_filtered_clauses:            1
% 7.09/1.50  num_of_subtypes:                        2
% 7.09/1.50  monotx_restored_types:                  0
% 7.09/1.50  sat_num_of_epr_types:                   0
% 7.09/1.50  sat_num_of_non_cyclic_types:            0
% 7.09/1.50  sat_guarded_non_collapsed_types:        1
% 7.09/1.50  num_pure_diseq_elim:                    0
% 7.09/1.50  simp_replaced_by:                       0
% 7.09/1.50  res_preprocessed:                       158
% 7.09/1.50  prep_upred:                             0
% 7.09/1.50  prep_unflattend:                        9
% 7.09/1.50  smt_new_axioms:                         0
% 7.09/1.50  pred_elim_cands:                        6
% 7.09/1.50  pred_elim:                              3
% 7.09/1.50  pred_elim_cl:                           5
% 7.09/1.50  pred_elim_cycles:                       6
% 7.09/1.50  merged_defs:                            0
% 7.09/1.50  merged_defs_ncl:                        0
% 7.09/1.50  bin_hyper_res:                          0
% 7.09/1.50  prep_cycles:                            4
% 7.09/1.50  pred_elim_time:                         0.006
% 7.09/1.50  splitting_time:                         0.
% 7.09/1.50  sem_filter_time:                        0.
% 7.09/1.50  monotx_time:                            0.
% 7.09/1.50  subtype_inf_time:                       0.001
% 7.09/1.50  
% 7.09/1.50  ------ Problem properties
% 7.09/1.50  
% 7.09/1.50  clauses:                                30
% 7.09/1.50  conjectures:                            14
% 7.09/1.50  epr:                                    10
% 7.09/1.50  horn:                                   21
% 7.09/1.50  ground:                                 14
% 7.09/1.50  unary:                                  15
% 7.09/1.50  binary:                                 3
% 7.09/1.50  lits:                                   128
% 7.09/1.50  lits_eq:                                16
% 7.09/1.50  fd_pure:                                0
% 7.09/1.50  fd_pseudo:                              0
% 7.09/1.50  fd_cond:                                0
% 7.09/1.50  fd_pseudo_cond:                         1
% 7.09/1.50  ac_symbols:                             0
% 7.09/1.50  
% 7.09/1.50  ------ Propositional Solver
% 7.09/1.50  
% 7.09/1.50  prop_solver_calls:                      30
% 7.09/1.50  prop_fast_solver_calls:                 2253
% 7.09/1.50  smt_solver_calls:                       0
% 7.09/1.50  smt_fast_solver_calls:                  0
% 7.09/1.50  prop_num_of_clauses:                    3711
% 7.09/1.50  prop_preprocess_simplified:             9229
% 7.09/1.50  prop_fo_subsumed:                       128
% 7.09/1.50  prop_solver_time:                       0.
% 7.09/1.50  smt_solver_time:                        0.
% 7.09/1.50  smt_fast_solver_time:                   0.
% 7.09/1.50  prop_fast_solver_time:                  0.
% 7.09/1.50  prop_unsat_core_time:                   0.
% 7.09/1.50  
% 7.09/1.50  ------ QBF
% 7.09/1.50  
% 7.09/1.50  qbf_q_res:                              0
% 7.09/1.50  qbf_num_tautologies:                    0
% 7.09/1.50  qbf_prep_cycles:                        0
% 7.09/1.50  
% 7.09/1.50  ------ BMC1
% 7.09/1.50  
% 7.09/1.50  bmc1_current_bound:                     -1
% 7.09/1.50  bmc1_last_solved_bound:                 -1
% 7.09/1.50  bmc1_unsat_core_size:                   -1
% 7.09/1.50  bmc1_unsat_core_parents_size:           -1
% 7.09/1.50  bmc1_merge_next_fun:                    0
% 7.09/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.09/1.50  
% 7.09/1.50  ------ Instantiation
% 7.09/1.50  
% 7.09/1.50  inst_num_of_clauses:                    982
% 7.09/1.50  inst_num_in_passive:                    197
% 7.09/1.50  inst_num_in_active:                     427
% 7.09/1.50  inst_num_in_unprocessed:                358
% 7.09/1.50  inst_num_of_loops:                      520
% 7.09/1.50  inst_num_of_learning_restarts:          0
% 7.09/1.50  inst_num_moves_active_passive:          91
% 7.09/1.50  inst_lit_activity:                      0
% 7.09/1.50  inst_lit_activity_moves:                1
% 7.09/1.50  inst_num_tautologies:                   0
% 7.09/1.50  inst_num_prop_implied:                  0
% 7.09/1.50  inst_num_existing_simplified:           0
% 7.09/1.50  inst_num_eq_res_simplified:             0
% 7.09/1.50  inst_num_child_elim:                    0
% 7.09/1.50  inst_num_of_dismatching_blockings:      84
% 7.09/1.50  inst_num_of_non_proper_insts:           715
% 7.09/1.50  inst_num_of_duplicates:                 0
% 7.09/1.50  inst_inst_num_from_inst_to_res:         0
% 7.09/1.50  inst_dismatching_checking_time:         0.
% 7.09/1.50  
% 7.09/1.50  ------ Resolution
% 7.09/1.50  
% 7.09/1.50  res_num_of_clauses:                     0
% 7.09/1.50  res_num_in_passive:                     0
% 7.09/1.50  res_num_in_active:                      0
% 7.09/1.50  res_num_of_loops:                       162
% 7.09/1.50  res_forward_subset_subsumed:            36
% 7.09/1.50  res_backward_subset_subsumed:           0
% 7.09/1.50  res_forward_subsumed:                   0
% 7.09/1.50  res_backward_subsumed:                  0
% 7.09/1.50  res_forward_subsumption_resolution:     1
% 7.09/1.50  res_backward_subsumption_resolution:    0
% 7.09/1.50  res_clause_to_clause_subsumption:       501
% 7.09/1.50  res_orphan_elimination:                 0
% 7.09/1.50  res_tautology_del:                      16
% 7.09/1.50  res_num_eq_res_simplified:              0
% 7.09/1.50  res_num_sel_changes:                    0
% 7.09/1.50  res_moves_from_active_to_pass:          0
% 7.09/1.50  
% 7.09/1.50  ------ Superposition
% 7.09/1.50  
% 7.09/1.50  sup_time_total:                         0.
% 7.09/1.50  sup_time_generating:                    0.
% 7.09/1.50  sup_time_sim_full:                      0.
% 7.09/1.50  sup_time_sim_immed:                     0.
% 7.09/1.50  
% 7.09/1.50  sup_num_of_clauses:                     152
% 7.09/1.50  sup_num_in_active:                      92
% 7.09/1.50  sup_num_in_passive:                     60
% 7.09/1.50  sup_num_of_loops:                       103
% 7.09/1.50  sup_fw_superposition:                   210
% 7.09/1.50  sup_bw_superposition:                   49
% 7.09/1.50  sup_immediate_simplified:               115
% 7.09/1.50  sup_given_eliminated:                   0
% 7.09/1.50  comparisons_done:                       0
% 7.09/1.50  comparisons_avoided:                    0
% 7.09/1.50  
% 7.09/1.50  ------ Simplifications
% 7.09/1.50  
% 7.09/1.50  
% 7.09/1.50  sim_fw_subset_subsumed:                 13
% 7.09/1.50  sim_bw_subset_subsumed:                 3
% 7.09/1.50  sim_fw_subsumed:                        21
% 7.09/1.50  sim_bw_subsumed:                        0
% 7.09/1.50  sim_fw_subsumption_res:                 0
% 7.09/1.50  sim_bw_subsumption_res:                 0
% 7.09/1.50  sim_tautology_del:                      0
% 7.09/1.50  sim_eq_tautology_del:                   2
% 7.09/1.50  sim_eq_res_simp:                        4
% 7.09/1.50  sim_fw_demodulated:                     61
% 7.09/1.50  sim_bw_demodulated:                     9
% 7.09/1.50  sim_light_normalised:                   23
% 7.09/1.50  sim_joinable_taut:                      0
% 7.09/1.50  sim_joinable_simp:                      0
% 7.09/1.50  sim_ac_normalised:                      0
% 7.09/1.50  sim_smt_subsumption:                    0
% 7.09/1.50  
%------------------------------------------------------------------------------
