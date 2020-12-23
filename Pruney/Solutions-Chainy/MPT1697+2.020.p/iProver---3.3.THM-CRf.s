%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:26 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 745 expanded)
%              Number of clauses        :  129 ( 200 expanded)
%              Number of leaves         :   23 ( 275 expanded)
%              Depth                    :   23
%              Number of atoms          : 1156 (9102 expanded)
%              Number of equality atoms :  261 (2015 expanded)
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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f48,f47,f46,f45,f44,f43])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f72,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f41])).

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
    inference(cnf_transformation,[],[f42])).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(cnf_transformation,[],[f35])).

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
    inference(cnf_transformation,[],[f35])).

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
    inference(cnf_transformation,[],[f35])).

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
    inference(cnf_transformation,[],[f42])).

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

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_846,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1620,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_853,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1614,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_2216,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1614])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_857,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_860,plain,
    ( r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1608,plain,
    ( k3_xboole_0(X0_53,X1_53) != k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_2300,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_857,c_1608])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_858,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1610,plain,
    ( r1_xboole_0(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X1_53,X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2478,plain,
    ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_1610])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_854,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1613,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_2943,plain,
    ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_1613])).

cnf(c_3719,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2216,c_2943])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_513,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_514,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_516,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_514,c_33,c_31])).

cnf(c_832,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_516])).

cnf(c_1634,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_859,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1609,plain,
    ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_3816,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1634,c_1609])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_840,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1626,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_840])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_856,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1611,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_2103,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1626,c_1611])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_843,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1623,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_852,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1615,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_2470,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1615])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_2051,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_4294,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2470,c_28,c_26,c_2051])).

cnf(c_2469,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_1615])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1832,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_852])).

cnf(c_2046,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_4193,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2469,c_25,c_23,c_2046])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_847,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_4196,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4193,c_847])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_864,plain,
    ( X0_53 != X1_53
    | X2_53 != X1_53
    | X2_53 = X0_53 ),
    theory(equality)).

cnf(c_1759,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0_53
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0_53
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_1959,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_862,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_1960,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_2207,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0_53
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0_53 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_3242,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2207])).

cnf(c_3243,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2046])).

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
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f71])).

cnf(c_190,plain,
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

cnf(c_191,plain,
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
    inference(renaming,[status(thm)],[c_190])).

cnf(c_834,plain,
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
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_1912,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(sK4,X3_53,X2_53)
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(X4_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X4_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X3_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X4_53,X3_53,X1_53)) != k2_partfun1(X3_53,X2_53,sK4,k9_subset_1(X4_53,X3_53,X1_53))
    | k2_partfun1(k4_subset_1(X4_53,X3_53,X1_53),X2_53,k1_tmap_1(X4_53,X2_53,X3_53,X1_53,sK4,X0_53),X3_53) = sK4 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_2171,plain,
    ( ~ v1_funct_2(sK5,X0_53,X1_53)
    | ~ v1_funct_2(sK4,X2_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(X3_53))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(X3_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X3_53)
    | v1_xboole_0(X0_53)
    | k2_partfun1(X0_53,X1_53,sK5,k9_subset_1(X3_53,X2_53,X0_53)) != k2_partfun1(X2_53,X1_53,sK4,k9_subset_1(X3_53,X2_53,X0_53))
    | k2_partfun1(k4_subset_1(X3_53,X2_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X2_53,X0_53,sK4,sK5),X2_53) = sK4 ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2555,plain,
    ( ~ v1_funct_2(sK5,X0_53,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_53))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | k2_partfun1(X0_53,sK1,sK5,k9_subset_1(X1_53,sK2,X0_53)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X1_53,sK2,X0_53),sK1,k1_tmap_1(X1_53,sK1,sK2,X0_53,sK4,sK5),sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_2903,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_53))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_53))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0_53,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0_53,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_3778,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2903])).

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
    inference(cnf_transformation,[],[f89])).

cnf(c_197,plain,
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

cnf(c_198,plain,
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
    inference(renaming,[status(thm)],[c_197])).

cnf(c_833,plain,
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
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_1902,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(sK4,X3_53,X2_53)
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(X4_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X4_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X3_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X4_53,X3_53,X1_53)) != k2_partfun1(X3_53,X2_53,sK4,k9_subset_1(X4_53,X3_53,X1_53))
    | k2_partfun1(k4_subset_1(X4_53,X3_53,X1_53),X2_53,k1_tmap_1(X4_53,X2_53,X3_53,X1_53,sK4,X0_53),X1_53) = X0_53 ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_2189,plain,
    ( ~ v1_funct_2(sK5,X0_53,X1_53)
    | ~ v1_funct_2(sK4,X2_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(X3_53))
    | ~ m1_subset_1(X2_53,k1_zfmisc_1(X3_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X3_53)
    | v1_xboole_0(X0_53)
    | k2_partfun1(X0_53,X1_53,sK5,k9_subset_1(X3_53,X2_53,X0_53)) != k2_partfun1(X2_53,X1_53,sK4,k9_subset_1(X3_53,X2_53,X0_53))
    | k2_partfun1(k4_subset_1(X3_53,X2_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X2_53,X0_53,sK4,sK5),X0_53) = sK5 ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_2575,plain,
    ( ~ v1_funct_2(sK5,X0_53,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_53))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | k2_partfun1(X0_53,sK1,sK5,k9_subset_1(X1_53,sK2,X0_53)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X1_53,sK2,X0_53),sK1,k1_tmap_1(X1_53,sK1,sK2,X0_53,sK4,sK5),X0_53) = sK5 ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_2924,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_53))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_53))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0_53,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0_53,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2575])).

cnf(c_3790,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_4213,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4196,c_35,c_34,c_33,c_32,c_31,c_30,c_28,c_27,c_26,c_25,c_24,c_23,c_847,c_1959,c_1960,c_3242,c_3243,c_3778,c_3790])).

cnf(c_4297,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_4294,c_4213])).

cnf(c_7026,plain,
    ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2103,c_4297])).

cnf(c_7027,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2103,c_7026])).

cnf(c_7220,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3816,c_7027])).

cnf(c_7327,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3816,c_7220])).

cnf(c_7328,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3719,c_7327])).

cnf(c_865,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(X2_53,X3_53)
    | X2_53 != X0_53
    | X3_53 != X1_53 ),
    theory(equality)).

cnf(c_1967,plain,
    ( r1_xboole_0(X0_53,X1_53)
    | ~ r1_xboole_0(X2_53,k1_xboole_0)
    | X0_53 != X2_53
    | X1_53 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_2344,plain,
    ( ~ r1_xboole_0(X0_53,k1_xboole_0)
    | r1_xboole_0(X1_53,k1_xboole_0)
    | X1_53 != X0_53
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_3444,plain,
    ( ~ r1_xboole_0(X0_53,k1_xboole_0)
    | r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
    | k1_relat_1(sK4) != X0_53
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2344])).

cnf(c_3446,plain,
    ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
    | ~ r1_xboole_0(sK2,k1_xboole_0)
    | k1_relat_1(sK4) != sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_2345,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1966,plain,
    ( ~ r1_xboole_0(X0_53,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,X0_53) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_2271,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_1925,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_2270,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_450,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_14])).

cnf(c_454,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_14,c_10,c_9])).

cnf(c_455,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_454])).

cnf(c_526,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_455])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_14,c_11,c_10,c_9])).

cnf(c_531,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_530])).

cnf(c_831,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_531])).

cnf(c_1827,plain,
    ( ~ v1_funct_2(sK4,X0_53,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2043,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_1744,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0)
    | k3_xboole_0(X0_53,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1746,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | k3_xboole_0(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1744])).

cnf(c_1724,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_899,plain,
    ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7328,c_3446,c_2345,c_2271,c_2270,c_2043,c_1746,c_1724,c_899,c_26,c_27,c_28,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:33:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.66/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/0.99  
% 3.66/0.99  ------  iProver source info
% 3.66/0.99  
% 3.66/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.66/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/0.99  git: non_committed_changes: false
% 3.66/0.99  git: last_make_outside_of_git: false
% 3.66/0.99  
% 3.66/0.99  ------ 
% 3.66/0.99  ------ Parsing...
% 3.66/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/0.99  
% 3.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.66/0.99  
% 3.66/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/0.99  
% 3.66/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/0.99  ------ Proving...
% 3.66/0.99  ------ Problem Properties 
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  clauses                                 30
% 3.66/0.99  conjectures                             13
% 3.66/0.99  EPR                                     10
% 3.66/0.99  Horn                                    23
% 3.66/0.99  unary                                   14
% 3.66/0.99  binary                                  5
% 3.66/0.99  lits                                    125
% 3.66/0.99  lits eq                                 16
% 3.66/0.99  fd_pure                                 0
% 3.66/0.99  fd_pseudo                               0
% 3.66/0.99  fd_cond                                 0
% 3.66/0.99  fd_pseudo_cond                          1
% 3.66/0.99  AC symbols                              0
% 3.66/0.99  
% 3.66/0.99  ------ Input Options Time Limit: Unbounded
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  ------ 
% 3.66/0.99  Current options:
% 3.66/0.99  ------ 
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  ------ Proving...
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  % SZS status Theorem for theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  fof(f15,conjecture,(
% 3.66/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f16,negated_conjecture,(
% 3.66/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.66/0.99    inference(negated_conjecture,[],[f15])).
% 3.66/0.99  
% 3.66/0.99  fof(f36,plain,(
% 3.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f16])).
% 3.66/0.99  
% 3.66/0.99  fof(f37,plain,(
% 3.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.66/0.99    inference(flattening,[],[f36])).
% 3.66/0.99  
% 3.66/0.99  fof(f48,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f47,plain,(
% 3.66/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f46,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f45,plain,(
% 3.66/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f44,plain,(
% 3.66/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f43,plain,(
% 3.66/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.66/0.99    introduced(choice_axiom,[])).
% 3.66/0.99  
% 3.66/0.99  fof(f49,plain,(
% 3.66/0.99    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.66/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f48,f47,f46,f45,f44,f43])).
% 3.66/0.99  
% 3.66/0.99  fof(f84,plain,(
% 3.66/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f8,axiom,(
% 3.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f24,plain,(
% 3.66/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.99    inference(ennf_transformation,[],[f8])).
% 3.66/0.99  
% 3.66/0.99  fof(f59,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.99    inference(cnf_transformation,[],[f24])).
% 3.66/0.99  
% 3.66/0.99  fof(f3,axiom,(
% 3.66/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f53,plain,(
% 3.66/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.66/0.99    inference(cnf_transformation,[],[f3])).
% 3.66/0.99  
% 3.66/0.99  fof(f1,axiom,(
% 3.66/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f38,plain,(
% 3.66/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.66/0.99    inference(nnf_transformation,[],[f1])).
% 3.66/0.99  
% 3.66/0.99  fof(f51,plain,(
% 3.66/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.66/0.99    inference(cnf_transformation,[],[f38])).
% 3.66/0.99  
% 3.66/0.99  fof(f2,axiom,(
% 3.66/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f18,plain,(
% 3.66/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.66/0.99    inference(ennf_transformation,[],[f2])).
% 3.66/0.99  
% 3.66/0.99  fof(f52,plain,(
% 3.66/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f18])).
% 3.66/0.99  
% 3.66/0.99  fof(f6,axiom,(
% 3.66/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f21,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f6])).
% 3.66/0.99  
% 3.66/0.99  fof(f56,plain,(
% 3.66/0.99    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f21])).
% 3.66/0.99  
% 3.66/0.99  fof(f7,axiom,(
% 3.66/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f22,plain,(
% 3.66/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f7])).
% 3.66/0.99  
% 3.66/0.99  fof(f23,plain,(
% 3.66/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.66/0.99    inference(flattening,[],[f22])).
% 3.66/0.99  
% 3.66/0.99  fof(f39,plain,(
% 3.66/0.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.66/0.99    inference(nnf_transformation,[],[f23])).
% 3.66/0.99  
% 3.66/0.99  fof(f57,plain,(
% 3.66/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f39])).
% 3.66/0.99  
% 3.66/0.99  fof(f78,plain,(
% 3.66/0.99    r1_subset_1(sK2,sK3)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f74,plain,(
% 3.66/0.99    ~v1_xboole_0(sK2)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f76,plain,(
% 3.66/0.99    ~v1_xboole_0(sK3)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f50,plain,(
% 3.66/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f38])).
% 3.66/0.99  
% 3.66/0.99  fof(f77,plain,(
% 3.66/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f4,axiom,(
% 3.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f19,plain,(
% 3.66/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f4])).
% 3.66/0.99  
% 3.66/0.99  fof(f54,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.66/0.99    inference(cnf_transformation,[],[f19])).
% 3.66/0.99  
% 3.66/0.99  fof(f81,plain,(
% 3.66/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f12,axiom,(
% 3.66/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f30,plain,(
% 3.66/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.66/0.99    inference(ennf_transformation,[],[f12])).
% 3.66/0.99  
% 3.66/0.99  fof(f31,plain,(
% 3.66/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.99    inference(flattening,[],[f30])).
% 3.66/0.99  
% 3.66/0.99  fof(f65,plain,(
% 3.66/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f31])).
% 3.66/0.99  
% 3.66/0.99  fof(f79,plain,(
% 3.66/0.99    v1_funct_1(sK4)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f82,plain,(
% 3.66/0.99    v1_funct_1(sK5)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f85,plain,(
% 3.66/0.99    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f72,plain,(
% 3.66/0.99    ~v1_xboole_0(sK0)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f73,plain,(
% 3.66/0.99    ~v1_xboole_0(sK1)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f75,plain,(
% 3.66/0.99    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f80,plain,(
% 3.66/0.99    v1_funct_2(sK4,sK2,sK1)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f83,plain,(
% 3.66/0.99    v1_funct_2(sK5,sK3,sK1)),
% 3.66/0.99    inference(cnf_transformation,[],[f49])).
% 3.66/0.99  
% 3.66/0.99  fof(f13,axiom,(
% 3.66/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f32,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.66/0.99    inference(ennf_transformation,[],[f13])).
% 3.66/0.99  
% 3.66/0.99  fof(f33,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.66/0.99    inference(flattening,[],[f32])).
% 3.66/0.99  
% 3.66/0.99  fof(f41,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.66/0.99    inference(nnf_transformation,[],[f33])).
% 3.66/0.99  
% 3.66/0.99  fof(f42,plain,(
% 3.66/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.66/0.99    inference(flattening,[],[f41])).
% 3.66/0.99  
% 3.66/0.99  fof(f66,plain,(
% 3.66/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f42])).
% 3.66/0.99  
% 3.66/0.99  fof(f90,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(equality_resolution,[],[f66])).
% 3.66/0.99  
% 3.66/0.99  fof(f14,axiom,(
% 3.66/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f34,plain,(
% 3.66/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.66/0.99    inference(ennf_transformation,[],[f14])).
% 3.66/0.99  
% 3.66/0.99  fof(f35,plain,(
% 3.66/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.66/0.99    inference(flattening,[],[f34])).
% 3.66/0.99  
% 3.66/0.99  fof(f69,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f35])).
% 3.66/0.99  
% 3.66/0.99  fof(f70,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f35])).
% 3.66/0.99  
% 3.66/0.99  fof(f71,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f35])).
% 3.66/0.99  
% 3.66/0.99  fof(f67,plain,(
% 3.66/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f42])).
% 3.66/0.99  
% 3.66/0.99  fof(f89,plain,(
% 3.66/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.66/0.99    inference(equality_resolution,[],[f67])).
% 3.66/0.99  
% 3.66/0.99  fof(f10,axiom,(
% 3.66/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f26,plain,(
% 3.66/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.66/0.99    inference(ennf_transformation,[],[f10])).
% 3.66/0.99  
% 3.66/0.99  fof(f27,plain,(
% 3.66/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.66/0.99    inference(flattening,[],[f26])).
% 3.66/0.99  
% 3.66/0.99  fof(f62,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f27])).
% 3.66/0.99  
% 3.66/0.99  fof(f9,axiom,(
% 3.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f17,plain,(
% 3.66/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.66/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.66/0.99  
% 3.66/0.99  fof(f25,plain,(
% 3.66/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/0.99    inference(ennf_transformation,[],[f17])).
% 3.66/0.99  
% 3.66/0.99  fof(f60,plain,(
% 3.66/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/0.99    inference(cnf_transformation,[],[f25])).
% 3.66/0.99  
% 3.66/0.99  fof(f11,axiom,(
% 3.66/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.66/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/0.99  
% 3.66/0.99  fof(f28,plain,(
% 3.66/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.66/0.99    inference(ennf_transformation,[],[f11])).
% 3.66/0.99  
% 3.66/0.99  fof(f29,plain,(
% 3.66/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.66/0.99    inference(flattening,[],[f28])).
% 3.66/0.99  
% 3.66/0.99  fof(f40,plain,(
% 3.66/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.66/0.99    inference(nnf_transformation,[],[f29])).
% 3.66/0.99  
% 3.66/0.99  fof(f63,plain,(
% 3.66/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.66/0.99    inference(cnf_transformation,[],[f40])).
% 3.66/0.99  
% 3.66/0.99  cnf(c_23,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.66/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_846,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1620,plain,
% 3.66/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_9,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | v1_relat_1(X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_853,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | v1_relat_1(X0_53) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1614,plain,
% 3.66/0.99      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 3.66/0.99      | v1_relat_1(X0_53) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2216,plain,
% 3.66/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1620,c_1614]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3,plain,
% 3.66/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.66/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_857,plain,
% 3.66/0.99      ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_0,plain,
% 3.66/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 3.66/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_860,plain,
% 3.66/0.99      ( r1_xboole_0(X0_53,X1_53)
% 3.66/0.99      | k3_xboole_0(X0_53,X1_53) != k1_xboole_0 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1608,plain,
% 3.66/0.99      ( k3_xboole_0(X0_53,X1_53) != k1_xboole_0
% 3.66/0.99      | r1_xboole_0(X0_53,X1_53) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2300,plain,
% 3.66/0.99      ( r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_857,c_1608]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_858,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,X1_53) | r1_xboole_0(X1_53,X0_53) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1610,plain,
% 3.66/0.99      ( r1_xboole_0(X0_53,X1_53) != iProver_top
% 3.66/0.99      | r1_xboole_0(X1_53,X0_53) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2478,plain,
% 3.66/0.99      ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2300,c_1610]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_6,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.66/0.99      | ~ v1_relat_1(X1)
% 3.66/0.99      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.66/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_854,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
% 3.66/0.99      | ~ v1_relat_1(X1_53)
% 3.66/0.99      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1613,plain,
% 3.66/0.99      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 3.66/0.99      | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
% 3.66/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2943,plain,
% 3.66/0.99      ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
% 3.66/0.99      | v1_relat_1(X0_53) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2478,c_1613]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3719,plain,
% 3.66/0.99      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2216,c_2943]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_8,plain,
% 3.66/0.99      ( ~ r1_subset_1(X0,X1)
% 3.66/0.99      | r1_xboole_0(X0,X1)
% 3.66/0.99      | v1_xboole_0(X0)
% 3.66/0.99      | v1_xboole_0(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_29,negated_conjecture,
% 3.66/0.99      ( r1_subset_1(sK2,sK3) ),
% 3.66/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_513,plain,
% 3.66/0.99      ( r1_xboole_0(X0,X1)
% 3.66/0.99      | v1_xboole_0(X0)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | sK3 != X1
% 3.66/0.99      | sK2 != X0 ),
% 3.66/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_514,plain,
% 3.66/0.99      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 3.66/0.99      inference(unflattening,[status(thm)],[c_513]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_33,negated_conjecture,
% 3.66/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.66/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_31,negated_conjecture,
% 3.66/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.66/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_516,plain,
% 3.66/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_514,c_33,c_31]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_832,plain,
% 3.66/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_516]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1634,plain,
% 3.66/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.66/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_859,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,X1_53)
% 3.66/0.99      | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1609,plain,
% 3.66/0.99      ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
% 3.66/0.99      | r1_xboole_0(X0_53,X1_53) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3816,plain,
% 3.66/0.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1634,c_1609]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_30,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.66/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_840,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_30]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1626,plain,
% 3.66/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_840]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.66/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_856,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 3.66/0.99      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1611,plain,
% 3.66/0.99      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 3.66/0.99      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2103,plain,
% 3.66/0.99      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1626,c_1611]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_26,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.66/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_843,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1623,plain,
% 3.66/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_15,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.66/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_852,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | ~ v1_funct_1(X0_53)
% 3.66/0.99      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1615,plain,
% 3.66/0.99      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 3.66/0.99      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.66/0.99      | v1_funct_1(X2_53) != iProver_top ),
% 3.66/0.99      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2470,plain,
% 3.66/0.99      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 3.66/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1623,c_1615]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_28,negated_conjecture,
% 3.66/0.99      ( v1_funct_1(sK4) ),
% 3.66/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1837,plain,
% 3.66/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_852]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2051,plain,
% 3.66/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1837]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4294,plain,
% 3.66/0.99      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_2470,c_28,c_26,c_2051]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2469,plain,
% 3.66/0.99      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 3.66/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_1620,c_1615]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_25,negated_conjecture,
% 3.66/0.99      ( v1_funct_1(sK5) ),
% 3.66/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1832,plain,
% 3.66/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_852]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2046,plain,
% 3.66/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1832]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4193,plain,
% 3.66/0.99      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_2469,c_25,c_23,c_2046]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_22,negated_conjecture,
% 3.66/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.66/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_847,negated_conjecture,
% 3.66/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.66/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4196,plain,
% 3.66/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.66/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_4193,c_847]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_35,negated_conjecture,
% 3.66/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.66/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_34,negated_conjecture,
% 3.66/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_32,negated_conjecture,
% 3.66/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 3.66/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_27,negated_conjecture,
% 3.66/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_24,negated_conjecture,
% 3.66/0.99      ( v1_funct_2(sK5,sK3,sK1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_864,plain,
% 3.66/0.99      ( X0_53 != X1_53 | X2_53 != X1_53 | X2_53 = X0_53 ),
% 3.66/0.99      theory(equality) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1759,plain,
% 3.66/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0_53
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0_53
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_864]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1959,plain,
% 3.66/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_862,plain,( X0_53 = X0_53 ),theory(equality) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1960,plain,
% 3.66/0.99      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_862]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2207,plain,
% 3.66/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0_53
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0_53 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_864]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3242,plain,
% 3.66/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
% 3.66/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2207]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3243,plain,
% 3.66/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2046]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_18,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.66/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_21,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_20,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_19,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1) ),
% 3.66/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_190,plain,
% 3.66/0.99      ( ~ v1_funct_1(X3)
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_18,c_21,c_20,c_19]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_191,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_190]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_834,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 3.66/0.99      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 3.66/0.99      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 3.66/0.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 3.66/0.99      | ~ v1_funct_1(X0_53)
% 3.66/0.99      | ~ v1_funct_1(X3_53)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X4_53)
% 3.66/0.99      | v1_xboole_0(X5_53)
% 3.66/0.99      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_191]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1912,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 3.66/0.99      | ~ v1_funct_2(sK4,X3_53,X2_53)
% 3.66/0.99      | ~ m1_subset_1(X3_53,k1_zfmisc_1(X4_53))
% 3.66/0.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X4_53))
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_53,X2_53)))
% 3.66/0.99      | ~ v1_funct_1(X0_53)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X4_53)
% 3.66/0.99      | v1_xboole_0(X3_53)
% 3.66/0.99      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X4_53,X3_53,X1_53)) != k2_partfun1(X3_53,X2_53,sK4,k9_subset_1(X4_53,X3_53,X1_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X4_53,X3_53,X1_53),X2_53,k1_tmap_1(X4_53,X2_53,X3_53,X1_53,sK4,X0_53),X3_53) = sK4 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_834]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2171,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,X0_53,X1_53)
% 3.66/0.99      | ~ v1_funct_2(sK4,X2_53,X1_53)
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(X3_53))
% 3.66/0.99      | ~ m1_subset_1(X2_53,k1_zfmisc_1(X3_53))
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X3_53)
% 3.66/0.99      | v1_xboole_0(X0_53)
% 3.66/0.99      | k2_partfun1(X0_53,X1_53,sK5,k9_subset_1(X3_53,X2_53,X0_53)) != k2_partfun1(X2_53,X1_53,sK4,k9_subset_1(X3_53,X2_53,X0_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X3_53,X2_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X2_53,X0_53,sK4,sK5),X2_53) = sK4 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1912]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2555,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,X0_53,sK1)
% 3.66/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_53))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X0_53)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | v1_xboole_0(sK2)
% 3.66/0.99      | k2_partfun1(X0_53,sK1,sK5,k9_subset_1(X1_53,sK2,X0_53)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1_53,sK2,X0_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X1_53,sK2,X0_53),sK1,k1_tmap_1(X1_53,sK1,sK2,X0_53,sK4,sK5),sK2) = sK4 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2171]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2903,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.66/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_53))
% 3.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_53))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X0_53)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | v1_xboole_0(sK3)
% 3.66/0.99      | v1_xboole_0(sK2)
% 3.66/0.99      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0_53,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0_53,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2555]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3778,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.66/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 3.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | v1_xboole_0(sK3)
% 3.66/0.99      | v1_xboole_0(sK2)
% 3.66/0.99      | v1_xboole_0(sK0)
% 3.66/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2903]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_17,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.66/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_197,plain,
% 3.66/0.99      ( ~ v1_funct_1(X3)
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_17,c_21,c_20,c_19]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_198,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.66/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | ~ v1_funct_1(X3)
% 3.66/0.99      | v1_xboole_0(X1)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | v1_xboole_0(X4)
% 3.66/0.99      | v1_xboole_0(X5)
% 3.66/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_197]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_833,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 3.66/0.99      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 3.66/0.99      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 3.66/0.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 3.66/0.99      | ~ v1_funct_1(X0_53)
% 3.66/0.99      | ~ v1_funct_1(X3_53)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X4_53)
% 3.66/0.99      | v1_xboole_0(X5_53)
% 3.66/0.99      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_198]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1902,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 3.66/0.99      | ~ v1_funct_2(sK4,X3_53,X2_53)
% 3.66/0.99      | ~ m1_subset_1(X3_53,k1_zfmisc_1(X4_53))
% 3.66/0.99      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X4_53))
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3_53,X2_53)))
% 3.66/0.99      | ~ v1_funct_1(X0_53)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X4_53)
% 3.66/0.99      | v1_xboole_0(X3_53)
% 3.66/0.99      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X4_53,X3_53,X1_53)) != k2_partfun1(X3_53,X2_53,sK4,k9_subset_1(X4_53,X3_53,X1_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X4_53,X3_53,X1_53),X2_53,k1_tmap_1(X4_53,X2_53,X3_53,X1_53,sK4,X0_53),X1_53) = X0_53 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_833]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2189,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,X0_53,X1_53)
% 3.66/0.99      | ~ v1_funct_2(sK4,X2_53,X1_53)
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(X3_53))
% 3.66/0.99      | ~ m1_subset_1(X2_53,k1_zfmisc_1(X3_53))
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X3_53)
% 3.66/0.99      | v1_xboole_0(X0_53)
% 3.66/0.99      | k2_partfun1(X0_53,X1_53,sK5,k9_subset_1(X3_53,X2_53,X0_53)) != k2_partfun1(X2_53,X1_53,sK4,k9_subset_1(X3_53,X2_53,X0_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X3_53,X2_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X2_53,X0_53,sK4,sK5),X0_53) = sK5 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1902]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2575,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,X0_53,sK1)
% 3.66/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1_53))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | v1_xboole_0(X0_53)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | v1_xboole_0(sK2)
% 3.66/0.99      | k2_partfun1(X0_53,sK1,sK5,k9_subset_1(X1_53,sK2,X0_53)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1_53,sK2,X0_53))
% 3.66/0.99      | k2_partfun1(k4_subset_1(X1_53,sK2,X0_53),sK1,k1_tmap_1(X1_53,sK1,sK2,X0_53,sK4,sK5),X0_53) = sK5 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2189]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2924,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.66/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0_53))
% 3.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0_53))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X0_53)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | v1_xboole_0(sK3)
% 3.66/0.99      | v1_xboole_0(sK2)
% 3.66/0.99      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0_53,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0_53,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2575]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3790,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.66/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 3.66/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 3.66/0.99      | ~ v1_funct_1(sK5)
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | v1_xboole_0(sK3)
% 3.66/0.99      | v1_xboole_0(sK2)
% 3.66/0.99      | v1_xboole_0(sK0)
% 3.66/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.66/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2924]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4213,plain,
% 3.66/0.99      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_4196,c_35,c_34,c_33,c_32,c_31,c_30,c_28,c_27,c_26,
% 3.66/0.99                 c_25,c_24,c_23,c_847,c_1959,c_1960,c_3242,c_3243,c_3778,
% 3.66/0.99                 c_3790]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_4297,plain,
% 3.66/0.99      ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_4294,c_4213]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7026,plain,
% 3.66/0.99      ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2103,c_4297]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7027,plain,
% 3.66/0.99      ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_2103,c_7026]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7220,plain,
% 3.66/0.99      ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_3816,c_7027]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7327,plain,
% 3.66/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_3816,c_7220]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_7328,plain,
% 3.66/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 3.66/0.99      inference(superposition,[status(thm)],[c_3719,c_7327]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_865,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,X1_53)
% 3.66/0.99      | r1_xboole_0(X2_53,X3_53)
% 3.66/0.99      | X2_53 != X0_53
% 3.66/0.99      | X3_53 != X1_53 ),
% 3.66/0.99      theory(equality) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1967,plain,
% 3.66/0.99      ( r1_xboole_0(X0_53,X1_53)
% 3.66/0.99      | ~ r1_xboole_0(X2_53,k1_xboole_0)
% 3.66/0.99      | X0_53 != X2_53
% 3.66/0.99      | X1_53 != k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_865]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2344,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,k1_xboole_0)
% 3.66/0.99      | r1_xboole_0(X1_53,k1_xboole_0)
% 3.66/0.99      | X1_53 != X0_53
% 3.66/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1967]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3444,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,k1_xboole_0)
% 3.66/0.99      | r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
% 3.66/0.99      | k1_relat_1(sK4) != X0_53
% 3.66/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_2344]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_3446,plain,
% 3.66/0.99      ( r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
% 3.66/0.99      | ~ r1_xboole_0(sK2,k1_xboole_0)
% 3.66/0.99      | k1_relat_1(sK4) != sK2
% 3.66/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_3444]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2345,plain,
% 3.66/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_862]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1966,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,k1_xboole_0)
% 3.66/0.99      | r1_xboole_0(k1_xboole_0,X0_53) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_858]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2271,plain,
% 3.66/0.99      ( ~ r1_xboole_0(k1_relat_1(sK4),k1_xboole_0)
% 3.66/0.99      | r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1966]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1925,plain,
% 3.66/0.99      ( ~ r1_xboole_0(X0_53,k1_relat_1(sK4))
% 3.66/0.99      | ~ v1_relat_1(sK4)
% 3.66/0.99      | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_854]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2270,plain,
% 3.66/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
% 3.66/0.99      | ~ v1_relat_1(sK4)
% 3.66/0.99      | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1925]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_11,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | v1_partfun1(X0,X1)
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | v1_xboole_0(X2) ),
% 3.66/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_10,plain,
% 3.66/0.99      ( v4_relat_1(X0,X1)
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.66/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_14,plain,
% 3.66/0.99      ( ~ v1_partfun1(X0,X1)
% 3.66/0.99      | ~ v4_relat_1(X0,X1)
% 3.66/0.99      | ~ v1_relat_1(X0)
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_450,plain,
% 3.66/0.99      ( ~ v1_partfun1(X0,X1)
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ v1_relat_1(X0)
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(resolution,[status(thm)],[c_10,c_14]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_454,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ v1_partfun1(X0,X1)
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_450,c_14,c_10,c_9]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_455,plain,
% 3.66/0.99      ( ~ v1_partfun1(X0,X1)
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_454]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_526,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(resolution,[status(thm)],[c_11,c_455]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_530,plain,
% 3.66/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(global_propositional_subsumption,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_526,c_14,c_11,c_10,c_9]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_531,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/0.99      | ~ v1_funct_1(X0)
% 3.66/0.99      | v1_xboole_0(X2)
% 3.66/0.99      | k1_relat_1(X0) = X1 ),
% 3.66/0.99      inference(renaming,[status(thm)],[c_530]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_831,plain,
% 3.66/0.99      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 3.66/0.99      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 3.66/0.99      | ~ v1_funct_1(X0_53)
% 3.66/0.99      | v1_xboole_0(X2_53)
% 3.66/0.99      | k1_relat_1(X0_53) = X1_53 ),
% 3.66/0.99      inference(subtyping,[status(esa)],[c_531]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1827,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK4,X0_53,X1_53)
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(X1_53)
% 3.66/0.99      | k1_relat_1(sK4) = X0_53 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_831]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_2043,plain,
% 3.66/0.99      ( ~ v1_funct_2(sK4,sK2,sK1)
% 3.66/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | ~ v1_funct_1(sK4)
% 3.66/0.99      | v1_xboole_0(sK1)
% 3.66/0.99      | k1_relat_1(sK4) = sK2 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1827]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1744,plain,
% 3.66/0.99      ( r1_xboole_0(X0_53,k1_xboole_0)
% 3.66/0.99      | k3_xboole_0(X0_53,k1_xboole_0) != k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_860]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1746,plain,
% 3.66/0.99      ( r1_xboole_0(sK2,k1_xboole_0)
% 3.66/0.99      | k3_xboole_0(sK2,k1_xboole_0) != k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_1744]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_1724,plain,
% 3.66/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.66/0.99      | v1_relat_1(sK4) ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_853]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(c_899,plain,
% 3.66/0.99      ( k3_xboole_0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 3.66/0.99      inference(instantiation,[status(thm)],[c_857]) ).
% 3.66/0.99  
% 3.66/0.99  cnf(contradiction,plain,
% 3.66/0.99      ( $false ),
% 3.66/0.99      inference(minisat,
% 3.66/0.99                [status(thm)],
% 3.66/0.99                [c_7328,c_3446,c_2345,c_2271,c_2270,c_2043,c_1746,c_1724,
% 3.66/0.99                 c_899,c_26,c_27,c_28,c_34]) ).
% 3.66/0.99  
% 3.66/0.99  
% 3.66/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/0.99  
% 3.66/0.99  ------                               Statistics
% 3.66/0.99  
% 3.66/0.99  ------ Selected
% 3.66/0.99  
% 3.66/0.99  total_time:                             0.338
% 3.66/0.99  
%------------------------------------------------------------------------------
