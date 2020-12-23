%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:36 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  225 (3421 expanded)
%              Number of clauses        :  145 ( 969 expanded)
%              Number of leaves         :   20 (1223 expanded)
%              Depth                    :   27
%              Number of atoms          : 1131 (38527 expanded)
%              Number of equality atoms :  433 (9062 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f35])).

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f47,f46,f45,f44,f43,f42])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f31])).

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
    inference(nnf_transformation,[],[f32])).

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
    inference(flattening,[],[f40])).

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
    inference(cnf_transformation,[],[f41])).

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
    inference(equality_resolution,[],[f63])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f33])).

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
    inference(cnf_transformation,[],[f34])).

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
    inference(cnf_transformation,[],[f34])).

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
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(cnf_transformation,[],[f41])).

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
    inference(equality_resolution,[],[f64])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_883,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1662,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_883])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_901,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | k9_subset_1(X1_52,X2_52,X0_52) = k3_xboole_0(X2_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1645,plain,
    ( k9_subset_1(X0_52,X1_52,X2_52) = k3_xboole_0(X1_52,X2_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_901])).

cnf(c_2323,plain,
    ( k9_subset_1(sK0,X0_52,sK3) = k3_xboole_0(X0_52,sK3) ),
    inference(superposition,[status(thm)],[c_1662,c_1645])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_886,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1659,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_886])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_895,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(X1_52,X2_52,X0_52,X3_52) = k7_relat_1(X0_52,X3_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1651,plain,
    ( k2_partfun1(X0_52,X1_52,X2_52,X3_52) = k7_relat_1(X2_52,X3_52)
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_895])).

cnf(c_3457,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_52) = k7_relat_1(sK4,X0_52)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_1651])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3577,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_52) = k7_relat_1(sK4,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3457,c_41])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_889,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1656,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_3456,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_52) = k7_relat_1(sK5,X0_52)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_1651])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_44,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3534,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_52) = k7_relat_1(sK5,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3456,c_44])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_19,plain,
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

cnf(c_18,plain,
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

cnf(c_17,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_19,c_18,c_17])).

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

cnf(c_877,plain,
    ( ~ v1_funct_2(X0_52,X1_52,X2_52)
    | ~ v1_funct_2(X3_52,X4_52,X2_52)
    | ~ m1_subset_1(X4_52,k1_zfmisc_1(X5_52))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(X5_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X2_52)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X3_52)
    | v1_xboole_0(X1_52)
    | v1_xboole_0(X2_52)
    | v1_xboole_0(X4_52)
    | v1_xboole_0(X5_52)
    | k2_partfun1(X1_52,X2_52,X0_52,k9_subset_1(X5_52,X4_52,X1_52)) != k2_partfun1(X4_52,X2_52,X3_52,k9_subset_1(X5_52,X4_52,X1_52))
    | k2_partfun1(k4_subset_1(X5_52,X4_52,X1_52),X2_52,k1_tmap_1(X5_52,X2_52,X4_52,X1_52,X3_52,X0_52),X4_52) = X3_52 ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_1668,plain,
    ( k2_partfun1(X0_52,X1_52,X2_52,k9_subset_1(X3_52,X4_52,X0_52)) != k2_partfun1(X4_52,X1_52,X5_52,k9_subset_1(X3_52,X4_52,X0_52))
    | k2_partfun1(k4_subset_1(X3_52,X4_52,X0_52),X1_52,k1_tmap_1(X3_52,X1_52,X4_52,X0_52,X5_52,X2_52),X4_52) = X5_52
    | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
    | v1_funct_2(X5_52,X4_52,X1_52) != iProver_top
    | m1_subset_1(X4_52,k1_zfmisc_1(X3_52)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X3_52)) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_funct_1(X5_52) != iProver_top
    | v1_xboole_0(X3_52) = iProver_top
    | v1_xboole_0(X1_52) = iProver_top
    | v1_xboole_0(X4_52) = iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_877])).

cnf(c_4981,plain,
    ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
    | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),X0_52) = X1_52
    | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(X2_52) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3534,c_1668])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_45,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_46,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5771,plain,
    ( v1_funct_1(X1_52) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),X0_52) = X1_52
    | k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
    | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(X2_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4981,c_35,c_38,c_44,c_45,c_46])).

cnf(c_5772,plain,
    ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
    | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),X0_52) = X1_52
    | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_xboole_0(X2_52) = iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_5771])).

cnf(c_5778,plain,
    ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_5772])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_42,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5892,plain,
    ( v1_xboole_0(X0_52) = iProver_top
    | k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5778,c_36,c_41,c_42,c_43])).

cnf(c_5893,plain,
    ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_5892])).

cnf(c_5898,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_5893])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_27,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_465,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_466,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_468,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_31,c_29])).

cnf(c_874,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_1671,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_874])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_903,plain,
    ( ~ r1_xboole_0(X0_52,X1_52)
    | k3_xboole_0(X0_52,X1_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1643,plain,
    ( k3_xboole_0(X0_52,X1_52) = k1_xboole_0
    | r1_xboole_0(X0_52,X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_903])).

cnf(c_2682,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1671,c_1643])).

cnf(c_5899,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5898,c_2682])).

cnf(c_5900,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5899,c_2323])).

cnf(c_5901,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5900,c_2682])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5902,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5901])).

cnf(c_15,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_19,c_18,c_17])).

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

cnf(c_876,plain,
    ( ~ v1_funct_2(X0_52,X1_52,X2_52)
    | ~ v1_funct_2(X3_52,X4_52,X2_52)
    | ~ m1_subset_1(X4_52,k1_zfmisc_1(X5_52))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(X5_52))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X2_52)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X3_52)
    | v1_xboole_0(X1_52)
    | v1_xboole_0(X2_52)
    | v1_xboole_0(X4_52)
    | v1_xboole_0(X5_52)
    | k2_partfun1(X1_52,X2_52,X0_52,k9_subset_1(X5_52,X4_52,X1_52)) != k2_partfun1(X4_52,X2_52,X3_52,k9_subset_1(X5_52,X4_52,X1_52))
    | k2_partfun1(k4_subset_1(X5_52,X4_52,X1_52),X2_52,k1_tmap_1(X5_52,X2_52,X4_52,X1_52,X3_52,X0_52),X1_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_194])).

cnf(c_1669,plain,
    ( k2_partfun1(X0_52,X1_52,X2_52,k9_subset_1(X3_52,X4_52,X0_52)) != k2_partfun1(X4_52,X1_52,X5_52,k9_subset_1(X3_52,X4_52,X0_52))
    | k2_partfun1(k4_subset_1(X3_52,X4_52,X0_52),X1_52,k1_tmap_1(X3_52,X1_52,X4_52,X0_52,X5_52,X2_52),X0_52) = X2_52
    | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
    | v1_funct_2(X5_52,X4_52,X1_52) != iProver_top
    | m1_subset_1(X4_52,k1_zfmisc_1(X3_52)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X3_52)) != iProver_top
    | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X1_52))) != iProver_top
    | v1_funct_1(X2_52) != iProver_top
    | v1_funct_1(X5_52) != iProver_top
    | v1_xboole_0(X3_52) = iProver_top
    | v1_xboole_0(X1_52) = iProver_top
    | v1_xboole_0(X4_52) = iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_876])).

cnf(c_6031,plain,
    ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
    | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),sK3) = sK5
    | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(X2_52) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3534,c_1669])).

cnf(c_7315,plain,
    ( v1_funct_1(X1_52) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),sK3) = sK5
    | k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
    | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(X2_52) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6031,c_35,c_38,c_44,c_45,c_46])).

cnf(c_7316,plain,
    ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
    | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),sK3) = sK5
    | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_xboole_0(X2_52) = iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_7315])).

cnf(c_7322,plain,
    ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3577,c_7316])).

cnf(c_7382,plain,
    ( v1_xboole_0(X0_52) = iProver_top
    | k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7322,c_36,c_41,c_42,c_43])).

cnf(c_7383,plain,
    ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
    | v1_xboole_0(X0_52) = iProver_top ),
    inference(renaming,[status(thm)],[c_7382])).

cnf(c_7388,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2323,c_7383])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_6])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_12,c_11,c_6])).

cnf(c_875,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | k7_relat_1(X0_52,X1_52) = X0_52 ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_1670,plain,
    ( k7_relat_1(X0_52,X1_52) = X0_52
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_875])).

cnf(c_6500,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_1656,c_1670])).

cnf(c_896,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1650,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_896])).

cnf(c_2608,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1656,c_1650])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_902,plain,
    ( ~ r1_xboole_0(X0_52,X1_52)
    | r1_xboole_0(X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1644,plain,
    ( r1_xboole_0(X0_52,X1_52) != iProver_top
    | r1_xboole_0(X1_52,X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_902])).

cnf(c_2684,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1644])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_899,plain,
    ( ~ r1_xboole_0(X0_52,X1_52)
    | ~ v1_relat_1(X2_52)
    | k7_relat_1(k7_relat_1(X2_52,X0_52),X1_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1647,plain,
    ( k7_relat_1(k7_relat_1(X0_52,X1_52),X2_52) = k1_xboole_0
    | r1_xboole_0(X1_52,X2_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_899])).

cnf(c_3511,plain,
    ( k7_relat_1(k7_relat_1(X0_52,sK3),sK2) = k1_xboole_0
    | v1_relat_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_2684,c_1647])).

cnf(c_3718,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK3),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2608,c_3511])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_897,plain,
    ( r1_xboole_0(k1_relat_1(X0_52),X1_52)
    | ~ v1_relat_1(X0_52)
    | k7_relat_1(X0_52,X1_52) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1649,plain,
    ( k7_relat_1(X0_52,X1_52) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_52),X1_52) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_897])).

cnf(c_3745,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK5,sK3)),sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3718,c_1649])).

cnf(c_3891,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK5,sK3)),sK2) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK5,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3745,c_1643])).

cnf(c_6506,plain,
    ( k3_xboole_0(k1_relat_1(sK5),sK2) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6500,c_3891])).

cnf(c_6643,plain,
    ( k3_xboole_0(k1_relat_1(sK5),sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6506,c_2608])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_900,plain,
    ( ~ v1_relat_1(X0_52)
    | k7_relat_1(X0_52,k3_xboole_0(k1_relat_1(X0_52),X1_52)) = k7_relat_1(X0_52,X1_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1646,plain,
    ( k7_relat_1(X0_52,k3_xboole_0(k1_relat_1(X0_52),X1_52)) = k7_relat_1(X0_52,X1_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_900])).

cnf(c_2852,plain,
    ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_52)) = k7_relat_1(sK5,X0_52) ),
    inference(superposition,[status(thm)],[c_2608,c_1646])).

cnf(c_6647,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_6643,c_2852])).

cnf(c_6509,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6500,c_3718])).

cnf(c_6650,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6647,c_6509])).

cnf(c_7389,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7388,c_2682,c_6650])).

cnf(c_7390,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7389,c_2323])).

cnf(c_6501,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_1659,c_1670])).

cnf(c_2609,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_1650])).

cnf(c_3510,plain,
    ( k7_relat_1(k7_relat_1(X0_52,sK2),sK3) = k1_xboole_0
    | v1_relat_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1671,c_1647])).

cnf(c_3582,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2609,c_3510])).

cnf(c_3667,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK4,sK2)),sK3) = iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3582,c_1649])).

cnf(c_3881,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK4,sK2)),sK3) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3667,c_1643])).

cnf(c_6555,plain,
    ( k3_xboole_0(k1_relat_1(sK4),sK3) = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6501,c_3881])).

cnf(c_6697,plain,
    ( k3_xboole_0(k1_relat_1(sK4),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6555,c_2609])).

cnf(c_2855,plain,
    ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_52)) = k7_relat_1(sK4,X0_52) ),
    inference(superposition,[status(thm)],[c_2609,c_1646])).

cnf(c_6701,plain,
    ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6697,c_2855])).

cnf(c_6558,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6501,c_3582])).

cnf(c_6704,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6701,c_6558])).

cnf(c_7391,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7390,c_2682,c_6704])).

cnf(c_7392,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7391])).

cnf(c_20,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_890,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2527,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2323,c_890])).

cnf(c_3243,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2682,c_2527])).

cnf(c_3537,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3534,c_3243])).

cnf(c_3716,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3537,c_3577])).

cnf(c_13254,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6650,c_3716])).

cnf(c_13255,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_13254,c_6704])).

cnf(c_13256,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_13255])).

cnf(c_15506,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5901,c_33,c_34,c_30,c_37,c_28,c_39,c_5902,c_7392,c_13256])).

cnf(c_15508,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15506,c_6650,c_6704])).

cnf(c_15509,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_15508])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.62/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/1.99  
% 11.62/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.62/1.99  
% 11.62/1.99  ------  iProver source info
% 11.62/1.99  
% 11.62/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.62/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.62/1.99  git: non_committed_changes: false
% 11.62/1.99  git: last_make_outside_of_git: false
% 11.62/1.99  
% 11.62/1.99  ------ 
% 11.62/1.99  
% 11.62/1.99  ------ Input Options
% 11.62/1.99  
% 11.62/1.99  --out_options                           all
% 11.62/1.99  --tptp_safe_out                         true
% 11.62/1.99  --problem_path                          ""
% 11.62/1.99  --include_path                          ""
% 11.62/1.99  --clausifier                            res/vclausify_rel
% 11.62/1.99  --clausifier_options                    ""
% 11.62/1.99  --stdin                                 false
% 11.62/1.99  --stats_out                             all
% 11.62/1.99  
% 11.62/1.99  ------ General Options
% 11.62/1.99  
% 11.62/1.99  --fof                                   false
% 11.62/1.99  --time_out_real                         305.
% 11.62/1.99  --time_out_virtual                      -1.
% 11.62/1.99  --symbol_type_check                     false
% 11.62/1.99  --clausify_out                          false
% 11.62/1.99  --sig_cnt_out                           false
% 11.62/1.99  --trig_cnt_out                          false
% 11.62/1.99  --trig_cnt_out_tolerance                1.
% 11.62/1.99  --trig_cnt_out_sk_spl                   false
% 11.62/1.99  --abstr_cl_out                          false
% 11.62/1.99  
% 11.62/1.99  ------ Global Options
% 11.62/1.99  
% 11.62/1.99  --schedule                              default
% 11.62/1.99  --add_important_lit                     false
% 11.62/1.99  --prop_solver_per_cl                    1000
% 11.62/1.99  --min_unsat_core                        false
% 11.62/1.99  --soft_assumptions                      false
% 11.62/1.99  --soft_lemma_size                       3
% 11.62/1.99  --prop_impl_unit_size                   0
% 11.62/1.99  --prop_impl_unit                        []
% 11.62/1.99  --share_sel_clauses                     true
% 11.62/1.99  --reset_solvers                         false
% 11.62/1.99  --bc_imp_inh                            [conj_cone]
% 11.62/1.99  --conj_cone_tolerance                   3.
% 11.62/1.99  --extra_neg_conj                        none
% 11.62/1.99  --large_theory_mode                     true
% 11.62/1.99  --prolific_symb_bound                   200
% 11.62/1.99  --lt_threshold                          2000
% 11.62/1.99  --clause_weak_htbl                      true
% 11.62/1.99  --gc_record_bc_elim                     false
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing Options
% 11.62/1.99  
% 11.62/1.99  --preprocessing_flag                    true
% 11.62/1.99  --time_out_prep_mult                    0.1
% 11.62/1.99  --splitting_mode                        input
% 11.62/1.99  --splitting_grd                         true
% 11.62/1.99  --splitting_cvd                         false
% 11.62/1.99  --splitting_cvd_svl                     false
% 11.62/1.99  --splitting_nvd                         32
% 11.62/1.99  --sub_typing                            true
% 11.62/1.99  --prep_gs_sim                           true
% 11.62/1.99  --prep_unflatten                        true
% 11.62/1.99  --prep_res_sim                          true
% 11.62/1.99  --prep_upred                            true
% 11.62/1.99  --prep_sem_filter                       exhaustive
% 11.62/1.99  --prep_sem_filter_out                   false
% 11.62/1.99  --pred_elim                             true
% 11.62/1.99  --res_sim_input                         true
% 11.62/1.99  --eq_ax_congr_red                       true
% 11.62/1.99  --pure_diseq_elim                       true
% 11.62/1.99  --brand_transform                       false
% 11.62/1.99  --non_eq_to_eq                          false
% 11.62/1.99  --prep_def_merge                        true
% 11.62/1.99  --prep_def_merge_prop_impl              false
% 11.62/1.99  --prep_def_merge_mbd                    true
% 11.62/1.99  --prep_def_merge_tr_red                 false
% 11.62/1.99  --prep_def_merge_tr_cl                  false
% 11.62/1.99  --smt_preprocessing                     true
% 11.62/1.99  --smt_ac_axioms                         fast
% 11.62/1.99  --preprocessed_out                      false
% 11.62/1.99  --preprocessed_stats                    false
% 11.62/1.99  
% 11.62/1.99  ------ Abstraction refinement Options
% 11.62/1.99  
% 11.62/1.99  --abstr_ref                             []
% 11.62/1.99  --abstr_ref_prep                        false
% 11.62/1.99  --abstr_ref_until_sat                   false
% 11.62/1.99  --abstr_ref_sig_restrict                funpre
% 11.62/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.62/1.99  --abstr_ref_under                       []
% 11.62/1.99  
% 11.62/1.99  ------ SAT Options
% 11.62/1.99  
% 11.62/1.99  --sat_mode                              false
% 11.62/1.99  --sat_fm_restart_options                ""
% 11.62/1.99  --sat_gr_def                            false
% 11.62/1.99  --sat_epr_types                         true
% 11.62/1.99  --sat_non_cyclic_types                  false
% 11.62/1.99  --sat_finite_models                     false
% 11.62/1.99  --sat_fm_lemmas                         false
% 11.62/1.99  --sat_fm_prep                           false
% 11.62/1.99  --sat_fm_uc_incr                        true
% 11.62/1.99  --sat_out_model                         small
% 11.62/1.99  --sat_out_clauses                       false
% 11.62/1.99  
% 11.62/1.99  ------ QBF Options
% 11.62/1.99  
% 11.62/1.99  --qbf_mode                              false
% 11.62/1.99  --qbf_elim_univ                         false
% 11.62/1.99  --qbf_dom_inst                          none
% 11.62/1.99  --qbf_dom_pre_inst                      false
% 11.62/1.99  --qbf_sk_in                             false
% 11.62/1.99  --qbf_pred_elim                         true
% 11.62/1.99  --qbf_split                             512
% 11.62/1.99  
% 11.62/1.99  ------ BMC1 Options
% 11.62/1.99  
% 11.62/1.99  --bmc1_incremental                      false
% 11.62/1.99  --bmc1_axioms                           reachable_all
% 11.62/1.99  --bmc1_min_bound                        0
% 11.62/1.99  --bmc1_max_bound                        -1
% 11.62/1.99  --bmc1_max_bound_default                -1
% 11.62/1.99  --bmc1_symbol_reachability              true
% 11.62/1.99  --bmc1_property_lemmas                  false
% 11.62/1.99  --bmc1_k_induction                      false
% 11.62/1.99  --bmc1_non_equiv_states                 false
% 11.62/1.99  --bmc1_deadlock                         false
% 11.62/1.99  --bmc1_ucm                              false
% 11.62/1.99  --bmc1_add_unsat_core                   none
% 11.62/1.99  --bmc1_unsat_core_children              false
% 11.62/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.62/1.99  --bmc1_out_stat                         full
% 11.62/1.99  --bmc1_ground_init                      false
% 11.62/1.99  --bmc1_pre_inst_next_state              false
% 11.62/1.99  --bmc1_pre_inst_state                   false
% 11.62/1.99  --bmc1_pre_inst_reach_state             false
% 11.62/1.99  --bmc1_out_unsat_core                   false
% 11.62/1.99  --bmc1_aig_witness_out                  false
% 11.62/1.99  --bmc1_verbose                          false
% 11.62/1.99  --bmc1_dump_clauses_tptp                false
% 11.62/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.62/1.99  --bmc1_dump_file                        -
% 11.62/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.62/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.62/1.99  --bmc1_ucm_extend_mode                  1
% 11.62/1.99  --bmc1_ucm_init_mode                    2
% 11.62/1.99  --bmc1_ucm_cone_mode                    none
% 11.62/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.62/1.99  --bmc1_ucm_relax_model                  4
% 11.62/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.62/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.62/1.99  --bmc1_ucm_layered_model                none
% 11.62/1.99  --bmc1_ucm_max_lemma_size               10
% 11.62/1.99  
% 11.62/1.99  ------ AIG Options
% 11.62/1.99  
% 11.62/1.99  --aig_mode                              false
% 11.62/1.99  
% 11.62/1.99  ------ Instantiation Options
% 11.62/1.99  
% 11.62/1.99  --instantiation_flag                    true
% 11.62/1.99  --inst_sos_flag                         true
% 11.62/1.99  --inst_sos_phase                        true
% 11.62/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.62/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.62/1.99  --inst_lit_sel_side                     num_symb
% 11.62/1.99  --inst_solver_per_active                1400
% 11.62/1.99  --inst_solver_calls_frac                1.
% 11.62/1.99  --inst_passive_queue_type               priority_queues
% 11.62/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.62/1.99  --inst_passive_queues_freq              [25;2]
% 11.62/1.99  --inst_dismatching                      true
% 11.62/1.99  --inst_eager_unprocessed_to_passive     true
% 11.62/1.99  --inst_prop_sim_given                   true
% 11.62/1.99  --inst_prop_sim_new                     false
% 11.62/1.99  --inst_subs_new                         false
% 11.62/1.99  --inst_eq_res_simp                      false
% 11.62/1.99  --inst_subs_given                       false
% 11.62/1.99  --inst_orphan_elimination               true
% 11.62/1.99  --inst_learning_loop_flag               true
% 11.62/1.99  --inst_learning_start                   3000
% 11.62/1.99  --inst_learning_factor                  2
% 11.62/1.99  --inst_start_prop_sim_after_learn       3
% 11.62/1.99  --inst_sel_renew                        solver
% 11.62/1.99  --inst_lit_activity_flag                true
% 11.62/1.99  --inst_restr_to_given                   false
% 11.62/1.99  --inst_activity_threshold               500
% 11.62/1.99  --inst_out_proof                        true
% 11.62/1.99  
% 11.62/1.99  ------ Resolution Options
% 11.62/1.99  
% 11.62/1.99  --resolution_flag                       true
% 11.62/1.99  --res_lit_sel                           adaptive
% 11.62/1.99  --res_lit_sel_side                      none
% 11.62/1.99  --res_ordering                          kbo
% 11.62/1.99  --res_to_prop_solver                    active
% 11.62/1.99  --res_prop_simpl_new                    false
% 11.62/1.99  --res_prop_simpl_given                  true
% 11.62/1.99  --res_passive_queue_type                priority_queues
% 11.62/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.62/1.99  --res_passive_queues_freq               [15;5]
% 11.62/1.99  --res_forward_subs                      full
% 11.62/1.99  --res_backward_subs                     full
% 11.62/1.99  --res_forward_subs_resolution           true
% 11.62/1.99  --res_backward_subs_resolution          true
% 11.62/1.99  --res_orphan_elimination                true
% 11.62/1.99  --res_time_limit                        2.
% 11.62/1.99  --res_out_proof                         true
% 11.62/1.99  
% 11.62/1.99  ------ Superposition Options
% 11.62/1.99  
% 11.62/1.99  --superposition_flag                    true
% 11.62/1.99  --sup_passive_queue_type                priority_queues
% 11.62/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.62/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.62/1.99  --demod_completeness_check              fast
% 11.62/1.99  --demod_use_ground                      true
% 11.62/1.99  --sup_to_prop_solver                    passive
% 11.62/1.99  --sup_prop_simpl_new                    true
% 11.62/1.99  --sup_prop_simpl_given                  true
% 11.62/1.99  --sup_fun_splitting                     true
% 11.62/1.99  --sup_smt_interval                      50000
% 11.62/1.99  
% 11.62/1.99  ------ Superposition Simplification Setup
% 11.62/1.99  
% 11.62/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.62/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.62/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.62/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.62/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.62/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.62/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.62/1.99  --sup_immed_triv                        [TrivRules]
% 11.62/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.99  --sup_immed_bw_main                     []
% 11.62/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.62/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.62/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.99  --sup_input_bw                          []
% 11.62/1.99  
% 11.62/1.99  ------ Combination Options
% 11.62/1.99  
% 11.62/1.99  --comb_res_mult                         3
% 11.62/1.99  --comb_sup_mult                         2
% 11.62/1.99  --comb_inst_mult                        10
% 11.62/1.99  
% 11.62/1.99  ------ Debug Options
% 11.62/1.99  
% 11.62/1.99  --dbg_backtrace                         false
% 11.62/1.99  --dbg_dump_prop_clauses                 false
% 11.62/1.99  --dbg_dump_prop_clauses_file            -
% 11.62/1.99  --dbg_out_stat                          false
% 11.62/1.99  ------ Parsing...
% 11.62/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/1.99  ------ Proving...
% 11.62/1.99  ------ Problem Properties 
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  clauses                                 31
% 11.62/1.99  conjectures                             13
% 11.62/1.99  EPR                                     10
% 11.62/1.99  Horn                                    25
% 11.62/1.99  unary                                   13
% 11.62/1.99  binary                                  7
% 11.62/1.99  lits                                    126
% 11.62/1.99  lits eq                                 18
% 11.62/1.99  fd_pure                                 0
% 11.62/1.99  fd_pseudo                               0
% 11.62/1.99  fd_cond                                 0
% 11.62/1.99  fd_pseudo_cond                          0
% 11.62/1.99  AC symbols                              0
% 11.62/1.99  
% 11.62/1.99  ------ Schedule dynamic 5 is on 
% 11.62/1.99  
% 11.62/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ 
% 11.62/1.99  Current options:
% 11.62/1.99  ------ 
% 11.62/1.99  
% 11.62/1.99  ------ Input Options
% 11.62/1.99  
% 11.62/1.99  --out_options                           all
% 11.62/1.99  --tptp_safe_out                         true
% 11.62/1.99  --problem_path                          ""
% 11.62/1.99  --include_path                          ""
% 11.62/1.99  --clausifier                            res/vclausify_rel
% 11.62/1.99  --clausifier_options                    ""
% 11.62/1.99  --stdin                                 false
% 11.62/1.99  --stats_out                             all
% 11.62/1.99  
% 11.62/1.99  ------ General Options
% 11.62/1.99  
% 11.62/1.99  --fof                                   false
% 11.62/1.99  --time_out_real                         305.
% 11.62/1.99  --time_out_virtual                      -1.
% 11.62/1.99  --symbol_type_check                     false
% 11.62/1.99  --clausify_out                          false
% 11.62/1.99  --sig_cnt_out                           false
% 11.62/1.99  --trig_cnt_out                          false
% 11.62/1.99  --trig_cnt_out_tolerance                1.
% 11.62/1.99  --trig_cnt_out_sk_spl                   false
% 11.62/1.99  --abstr_cl_out                          false
% 11.62/1.99  
% 11.62/1.99  ------ Global Options
% 11.62/1.99  
% 11.62/1.99  --schedule                              default
% 11.62/1.99  --add_important_lit                     false
% 11.62/1.99  --prop_solver_per_cl                    1000
% 11.62/1.99  --min_unsat_core                        false
% 11.62/1.99  --soft_assumptions                      false
% 11.62/1.99  --soft_lemma_size                       3
% 11.62/1.99  --prop_impl_unit_size                   0
% 11.62/1.99  --prop_impl_unit                        []
% 11.62/1.99  --share_sel_clauses                     true
% 11.62/1.99  --reset_solvers                         false
% 11.62/1.99  --bc_imp_inh                            [conj_cone]
% 11.62/1.99  --conj_cone_tolerance                   3.
% 11.62/1.99  --extra_neg_conj                        none
% 11.62/1.99  --large_theory_mode                     true
% 11.62/1.99  --prolific_symb_bound                   200
% 11.62/1.99  --lt_threshold                          2000
% 11.62/1.99  --clause_weak_htbl                      true
% 11.62/1.99  --gc_record_bc_elim                     false
% 11.62/1.99  
% 11.62/1.99  ------ Preprocessing Options
% 11.62/1.99  
% 11.62/1.99  --preprocessing_flag                    true
% 11.62/1.99  --time_out_prep_mult                    0.1
% 11.62/1.99  --splitting_mode                        input
% 11.62/1.99  --splitting_grd                         true
% 11.62/1.99  --splitting_cvd                         false
% 11.62/1.99  --splitting_cvd_svl                     false
% 11.62/1.99  --splitting_nvd                         32
% 11.62/1.99  --sub_typing                            true
% 11.62/1.99  --prep_gs_sim                           true
% 11.62/1.99  --prep_unflatten                        true
% 11.62/1.99  --prep_res_sim                          true
% 11.62/1.99  --prep_upred                            true
% 11.62/1.99  --prep_sem_filter                       exhaustive
% 11.62/1.99  --prep_sem_filter_out                   false
% 11.62/1.99  --pred_elim                             true
% 11.62/1.99  --res_sim_input                         true
% 11.62/1.99  --eq_ax_congr_red                       true
% 11.62/1.99  --pure_diseq_elim                       true
% 11.62/1.99  --brand_transform                       false
% 11.62/1.99  --non_eq_to_eq                          false
% 11.62/1.99  --prep_def_merge                        true
% 11.62/1.99  --prep_def_merge_prop_impl              false
% 11.62/1.99  --prep_def_merge_mbd                    true
% 11.62/1.99  --prep_def_merge_tr_red                 false
% 11.62/1.99  --prep_def_merge_tr_cl                  false
% 11.62/1.99  --smt_preprocessing                     true
% 11.62/1.99  --smt_ac_axioms                         fast
% 11.62/1.99  --preprocessed_out                      false
% 11.62/1.99  --preprocessed_stats                    false
% 11.62/1.99  
% 11.62/1.99  ------ Abstraction refinement Options
% 11.62/1.99  
% 11.62/1.99  --abstr_ref                             []
% 11.62/1.99  --abstr_ref_prep                        false
% 11.62/1.99  --abstr_ref_until_sat                   false
% 11.62/1.99  --abstr_ref_sig_restrict                funpre
% 11.62/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.62/1.99  --abstr_ref_under                       []
% 11.62/1.99  
% 11.62/1.99  ------ SAT Options
% 11.62/1.99  
% 11.62/1.99  --sat_mode                              false
% 11.62/1.99  --sat_fm_restart_options                ""
% 11.62/1.99  --sat_gr_def                            false
% 11.62/1.99  --sat_epr_types                         true
% 11.62/1.99  --sat_non_cyclic_types                  false
% 11.62/1.99  --sat_finite_models                     false
% 11.62/1.99  --sat_fm_lemmas                         false
% 11.62/1.99  --sat_fm_prep                           false
% 11.62/1.99  --sat_fm_uc_incr                        true
% 11.62/1.99  --sat_out_model                         small
% 11.62/1.99  --sat_out_clauses                       false
% 11.62/1.99  
% 11.62/1.99  ------ QBF Options
% 11.62/1.99  
% 11.62/1.99  --qbf_mode                              false
% 11.62/1.99  --qbf_elim_univ                         false
% 11.62/1.99  --qbf_dom_inst                          none
% 11.62/1.99  --qbf_dom_pre_inst                      false
% 11.62/1.99  --qbf_sk_in                             false
% 11.62/1.99  --qbf_pred_elim                         true
% 11.62/1.99  --qbf_split                             512
% 11.62/1.99  
% 11.62/1.99  ------ BMC1 Options
% 11.62/1.99  
% 11.62/1.99  --bmc1_incremental                      false
% 11.62/1.99  --bmc1_axioms                           reachable_all
% 11.62/1.99  --bmc1_min_bound                        0
% 11.62/1.99  --bmc1_max_bound                        -1
% 11.62/1.99  --bmc1_max_bound_default                -1
% 11.62/1.99  --bmc1_symbol_reachability              true
% 11.62/1.99  --bmc1_property_lemmas                  false
% 11.62/1.99  --bmc1_k_induction                      false
% 11.62/1.99  --bmc1_non_equiv_states                 false
% 11.62/1.99  --bmc1_deadlock                         false
% 11.62/1.99  --bmc1_ucm                              false
% 11.62/1.99  --bmc1_add_unsat_core                   none
% 11.62/1.99  --bmc1_unsat_core_children              false
% 11.62/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.62/1.99  --bmc1_out_stat                         full
% 11.62/1.99  --bmc1_ground_init                      false
% 11.62/1.99  --bmc1_pre_inst_next_state              false
% 11.62/1.99  --bmc1_pre_inst_state                   false
% 11.62/1.99  --bmc1_pre_inst_reach_state             false
% 11.62/1.99  --bmc1_out_unsat_core                   false
% 11.62/1.99  --bmc1_aig_witness_out                  false
% 11.62/1.99  --bmc1_verbose                          false
% 11.62/1.99  --bmc1_dump_clauses_tptp                false
% 11.62/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.62/1.99  --bmc1_dump_file                        -
% 11.62/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.62/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.62/1.99  --bmc1_ucm_extend_mode                  1
% 11.62/1.99  --bmc1_ucm_init_mode                    2
% 11.62/1.99  --bmc1_ucm_cone_mode                    none
% 11.62/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.62/1.99  --bmc1_ucm_relax_model                  4
% 11.62/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.62/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.62/1.99  --bmc1_ucm_layered_model                none
% 11.62/1.99  --bmc1_ucm_max_lemma_size               10
% 11.62/1.99  
% 11.62/1.99  ------ AIG Options
% 11.62/1.99  
% 11.62/1.99  --aig_mode                              false
% 11.62/1.99  
% 11.62/1.99  ------ Instantiation Options
% 11.62/1.99  
% 11.62/1.99  --instantiation_flag                    true
% 11.62/1.99  --inst_sos_flag                         true
% 11.62/1.99  --inst_sos_phase                        true
% 11.62/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.62/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.62/1.99  --inst_lit_sel_side                     none
% 11.62/1.99  --inst_solver_per_active                1400
% 11.62/1.99  --inst_solver_calls_frac                1.
% 11.62/1.99  --inst_passive_queue_type               priority_queues
% 11.62/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.62/1.99  --inst_passive_queues_freq              [25;2]
% 11.62/1.99  --inst_dismatching                      true
% 11.62/1.99  --inst_eager_unprocessed_to_passive     true
% 11.62/1.99  --inst_prop_sim_given                   true
% 11.62/1.99  --inst_prop_sim_new                     false
% 11.62/1.99  --inst_subs_new                         false
% 11.62/1.99  --inst_eq_res_simp                      false
% 11.62/1.99  --inst_subs_given                       false
% 11.62/1.99  --inst_orphan_elimination               true
% 11.62/1.99  --inst_learning_loop_flag               true
% 11.62/1.99  --inst_learning_start                   3000
% 11.62/1.99  --inst_learning_factor                  2
% 11.62/1.99  --inst_start_prop_sim_after_learn       3
% 11.62/1.99  --inst_sel_renew                        solver
% 11.62/1.99  --inst_lit_activity_flag                true
% 11.62/1.99  --inst_restr_to_given                   false
% 11.62/1.99  --inst_activity_threshold               500
% 11.62/1.99  --inst_out_proof                        true
% 11.62/1.99  
% 11.62/1.99  ------ Resolution Options
% 11.62/1.99  
% 11.62/1.99  --resolution_flag                       false
% 11.62/1.99  --res_lit_sel                           adaptive
% 11.62/1.99  --res_lit_sel_side                      none
% 11.62/1.99  --res_ordering                          kbo
% 11.62/1.99  --res_to_prop_solver                    active
% 11.62/1.99  --res_prop_simpl_new                    false
% 11.62/1.99  --res_prop_simpl_given                  true
% 11.62/1.99  --res_passive_queue_type                priority_queues
% 11.62/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.62/1.99  --res_passive_queues_freq               [15;5]
% 11.62/1.99  --res_forward_subs                      full
% 11.62/1.99  --res_backward_subs                     full
% 11.62/1.99  --res_forward_subs_resolution           true
% 11.62/1.99  --res_backward_subs_resolution          true
% 11.62/1.99  --res_orphan_elimination                true
% 11.62/1.99  --res_time_limit                        2.
% 11.62/1.99  --res_out_proof                         true
% 11.62/1.99  
% 11.62/1.99  ------ Superposition Options
% 11.62/1.99  
% 11.62/1.99  --superposition_flag                    true
% 11.62/1.99  --sup_passive_queue_type                priority_queues
% 11.62/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.62/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.62/1.99  --demod_completeness_check              fast
% 11.62/1.99  --demod_use_ground                      true
% 11.62/1.99  --sup_to_prop_solver                    passive
% 11.62/1.99  --sup_prop_simpl_new                    true
% 11.62/1.99  --sup_prop_simpl_given                  true
% 11.62/1.99  --sup_fun_splitting                     true
% 11.62/1.99  --sup_smt_interval                      50000
% 11.62/1.99  
% 11.62/1.99  ------ Superposition Simplification Setup
% 11.62/1.99  
% 11.62/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.62/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.62/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.62/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.62/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.62/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.62/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.62/1.99  --sup_immed_triv                        [TrivRules]
% 11.62/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.99  --sup_immed_bw_main                     []
% 11.62/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.62/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.62/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/1.99  --sup_input_bw                          []
% 11.62/1.99  
% 11.62/1.99  ------ Combination Options
% 11.62/1.99  
% 11.62/1.99  --comb_res_mult                         3
% 11.62/1.99  --comb_sup_mult                         2
% 11.62/1.99  --comb_inst_mult                        10
% 11.62/1.99  
% 11.62/1.99  ------ Debug Options
% 11.62/1.99  
% 11.62/1.99  --dbg_backtrace                         false
% 11.62/1.99  --dbg_dump_prop_clauses                 false
% 11.62/1.99  --dbg_dump_prop_clauses_file            -
% 11.62/1.99  --dbg_out_stat                          false
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  ------ Proving...
% 11.62/1.99  
% 11.62/1.99  
% 11.62/1.99  % SZS status Theorem for theBenchmark.p
% 11.62/1.99  
% 11.62/1.99   Resolution empty clause
% 11.62/1.99  
% 11.62/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.62/1.99  
% 11.62/1.99  fof(f14,conjecture,(
% 11.62/1.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f15,negated_conjecture,(
% 11.62/1.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.62/1.99    inference(negated_conjecture,[],[f14])).
% 11.62/1.99  
% 11.62/1.99  fof(f35,plain,(
% 11.62/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.62/1.99    inference(ennf_transformation,[],[f15])).
% 11.62/1.99  
% 11.62/1.99  fof(f36,plain,(
% 11.62/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.62/1.99    inference(flattening,[],[f35])).
% 11.62/1.99  
% 11.62/1.99  fof(f47,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f46,plain,(
% 11.62/1.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f45,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f44,plain,(
% 11.62/1.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f43,plain,(
% 11.62/1.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f42,plain,(
% 11.62/1.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 11.62/1.99    introduced(choice_axiom,[])).
% 11.62/1.99  
% 11.62/1.99  fof(f48,plain,(
% 11.62/1.99    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 11.62/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f47,f46,f45,f44,f43,f42])).
% 11.62/1.99  
% 11.62/1.99  fof(f74,plain,(
% 11.62/1.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f3,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f18,plain,(
% 11.62/1.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.62/1.99    inference(ennf_transformation,[],[f3])).
% 11.62/1.99  
% 11.62/1.99  fof(f52,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.62/1.99    inference(cnf_transformation,[],[f18])).
% 11.62/1.99  
% 11.62/1.99  fof(f78,plain,(
% 11.62/1.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f11,axiom,(
% 11.62/1.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f29,plain,(
% 11.62/1.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.62/1.99    inference(ennf_transformation,[],[f11])).
% 11.62/1.99  
% 11.62/1.99  fof(f30,plain,(
% 11.62/1.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.62/1.99    inference(flattening,[],[f29])).
% 11.62/1.99  
% 11.62/1.99  fof(f62,plain,(
% 11.62/1.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f30])).
% 11.62/1.99  
% 11.62/1.99  fof(f76,plain,(
% 11.62/1.99    v1_funct_1(sK4)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f81,plain,(
% 11.62/1.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f79,plain,(
% 11.62/1.99    v1_funct_1(sK5)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f12,axiom,(
% 11.62/1.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f31,plain,(
% 11.62/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/1.99    inference(ennf_transformation,[],[f12])).
% 11.62/1.99  
% 11.62/1.99  fof(f32,plain,(
% 11.62/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/1.99    inference(flattening,[],[f31])).
% 11.62/1.99  
% 11.62/1.99  fof(f40,plain,(
% 11.62/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/1.99    inference(nnf_transformation,[],[f32])).
% 11.62/1.99  
% 11.62/1.99  fof(f41,plain,(
% 11.62/1.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/1.99    inference(flattening,[],[f40])).
% 11.62/1.99  
% 11.62/1.99  fof(f63,plain,(
% 11.62/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f41])).
% 11.62/1.99  
% 11.62/1.99  fof(f86,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(equality_resolution,[],[f63])).
% 11.62/1.99  
% 11.62/1.99  fof(f13,axiom,(
% 11.62/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f33,plain,(
% 11.62/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.62/1.99    inference(ennf_transformation,[],[f13])).
% 11.62/1.99  
% 11.62/1.99  fof(f34,plain,(
% 11.62/1.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.62/1.99    inference(flattening,[],[f33])).
% 11.62/1.99  
% 11.62/1.99  fof(f66,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f34])).
% 11.62/1.99  
% 11.62/1.99  fof(f67,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f34])).
% 11.62/1.99  
% 11.62/1.99  fof(f68,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f34])).
% 11.62/1.99  
% 11.62/1.99  fof(f70,plain,(
% 11.62/1.99    ~v1_xboole_0(sK1)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f73,plain,(
% 11.62/1.99    ~v1_xboole_0(sK3)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f80,plain,(
% 11.62/1.99    v1_funct_2(sK5,sK3,sK1)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f71,plain,(
% 11.62/1.99    ~v1_xboole_0(sK2)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f77,plain,(
% 11.62/1.99    v1_funct_2(sK4,sK2,sK1)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f8,axiom,(
% 11.62/1.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f25,plain,(
% 11.62/1.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.62/1.99    inference(ennf_transformation,[],[f8])).
% 11.62/1.99  
% 11.62/1.99  fof(f26,plain,(
% 11.62/1.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.62/1.99    inference(flattening,[],[f25])).
% 11.62/1.99  
% 11.62/1.99  fof(f39,plain,(
% 11.62/1.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.62/1.99    inference(nnf_transformation,[],[f26])).
% 11.62/1.99  
% 11.62/1.99  fof(f58,plain,(
% 11.62/1.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f39])).
% 11.62/1.99  
% 11.62/1.99  fof(f75,plain,(
% 11.62/1.99    r1_subset_1(sK2,sK3)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f1,axiom,(
% 11.62/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f37,plain,(
% 11.62/1.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.62/1.99    inference(nnf_transformation,[],[f1])).
% 11.62/1.99  
% 11.62/1.99  fof(f49,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f37])).
% 11.62/1.99  
% 11.62/1.99  fof(f69,plain,(
% 11.62/1.99    ~v1_xboole_0(sK0)),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f72,plain,(
% 11.62/1.99    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  fof(f64,plain,(
% 11.62/1.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f41])).
% 11.62/1.99  
% 11.62/1.99  fof(f85,plain,(
% 11.62/1.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/1.99    inference(equality_resolution,[],[f64])).
% 11.62/1.99  
% 11.62/1.99  fof(f10,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f16,plain,(
% 11.62/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.62/1.99    inference(pure_predicate_removal,[],[f10])).
% 11.62/1.99  
% 11.62/1.99  fof(f28,plain,(
% 11.62/1.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/1.99    inference(ennf_transformation,[],[f16])).
% 11.62/1.99  
% 11.62/1.99  fof(f61,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/1.99    inference(cnf_transformation,[],[f28])).
% 11.62/1.99  
% 11.62/1.99  fof(f6,axiom,(
% 11.62/1.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f22,plain,(
% 11.62/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.62/1.99    inference(ennf_transformation,[],[f6])).
% 11.62/1.99  
% 11.62/1.99  fof(f23,plain,(
% 11.62/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.62/1.99    inference(flattening,[],[f22])).
% 11.62/1.99  
% 11.62/1.99  fof(f55,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f23])).
% 11.62/1.99  
% 11.62/1.99  fof(f9,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f27,plain,(
% 11.62/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/1.99    inference(ennf_transformation,[],[f9])).
% 11.62/1.99  
% 11.62/1.99  fof(f60,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/1.99    inference(cnf_transformation,[],[f27])).
% 11.62/1.99  
% 11.62/1.99  fof(f2,axiom,(
% 11.62/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f17,plain,(
% 11.62/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.62/1.99    inference(ennf_transformation,[],[f2])).
% 11.62/1.99  
% 11.62/1.99  fof(f51,plain,(
% 11.62/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f17])).
% 11.62/1.99  
% 11.62/1.99  fof(f5,axiom,(
% 11.62/1.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f20,plain,(
% 11.62/1.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.62/1.99    inference(ennf_transformation,[],[f5])).
% 11.62/1.99  
% 11.62/1.99  fof(f21,plain,(
% 11.62/1.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 11.62/1.99    inference(flattening,[],[f20])).
% 11.62/1.99  
% 11.62/1.99  fof(f54,plain,(
% 11.62/1.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f21])).
% 11.62/1.99  
% 11.62/1.99  fof(f7,axiom,(
% 11.62/1.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f24,plain,(
% 11.62/1.99    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.62/1.99    inference(ennf_transformation,[],[f7])).
% 11.62/1.99  
% 11.62/1.99  fof(f38,plain,(
% 11.62/1.99    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.62/1.99    inference(nnf_transformation,[],[f24])).
% 11.62/1.99  
% 11.62/1.99  fof(f56,plain,(
% 11.62/1.99    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f38])).
% 11.62/1.99  
% 11.62/1.99  fof(f4,axiom,(
% 11.62/1.99    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 11.62/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/1.99  
% 11.62/1.99  fof(f19,plain,(
% 11.62/1.99    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.62/1.99    inference(ennf_transformation,[],[f4])).
% 11.62/1.99  
% 11.62/1.99  fof(f53,plain,(
% 11.62/1.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.62/1.99    inference(cnf_transformation,[],[f19])).
% 11.62/1.99  
% 11.62/1.99  fof(f82,plain,(
% 11.62/1.99    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 11.62/1.99    inference(cnf_transformation,[],[f48])).
% 11.62/1.99  
% 11.62/1.99  cnf(c_28,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.62/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_883,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_28]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1662,plain,
% 11.62/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_883]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_3,plain,
% 11.62/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/1.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.62/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_901,plain,
% 11.62/1.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 11.62/1.99      | k9_subset_1(X1_52,X2_52,X0_52) = k3_xboole_0(X2_52,X0_52) ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_3]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1645,plain,
% 11.62/1.99      ( k9_subset_1(X0_52,X1_52,X2_52) = k3_xboole_0(X1_52,X2_52)
% 11.62/1.99      | m1_subset_1(X2_52,k1_zfmisc_1(X0_52)) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_901]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_2323,plain,
% 11.62/1.99      ( k9_subset_1(sK0,X0_52,sK3) = k3_xboole_0(X0_52,sK3) ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_1662,c_1645]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_24,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.62/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_886,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_24]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1659,plain,
% 11.62/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_886]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_13,plain,
% 11.62/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.62/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_895,plain,
% 11.62/1.99      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 11.62/1.99      | ~ v1_funct_1(X0_52)
% 11.62/1.99      | k2_partfun1(X1_52,X2_52,X0_52,X3_52) = k7_relat_1(X0_52,X3_52) ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_13]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1651,plain,
% 11.62/1.99      ( k2_partfun1(X0_52,X1_52,X2_52,X3_52) = k7_relat_1(X2_52,X3_52)
% 11.62/1.99      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 11.62/1.99      | v1_funct_1(X2_52) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_895]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_3457,plain,
% 11.62/1.99      ( k2_partfun1(sK2,sK1,sK4,X0_52) = k7_relat_1(sK4,X0_52)
% 11.62/1.99      | v1_funct_1(sK4) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_1659,c_1651]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_26,negated_conjecture,
% 11.62/1.99      ( v1_funct_1(sK4) ),
% 11.62/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_41,plain,
% 11.62/1.99      ( v1_funct_1(sK4) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_3577,plain,
% 11.62/1.99      ( k2_partfun1(sK2,sK1,sK4,X0_52) = k7_relat_1(sK4,X0_52) ),
% 11.62/1.99      inference(global_propositional_subsumption,[status(thm)],[c_3457,c_41]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_21,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.62/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_889,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_21]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1656,plain,
% 11.62/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_3456,plain,
% 11.62/1.99      ( k2_partfun1(sK3,sK1,sK5,X0_52) = k7_relat_1(sK5,X0_52)
% 11.62/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_1656,c_1651]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_23,negated_conjecture,
% 11.62/1.99      ( v1_funct_1(sK5) ),
% 11.62/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_44,plain,
% 11.62/1.99      ( v1_funct_1(sK5) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_3534,plain,
% 11.62/1.99      ( k2_partfun1(sK3,sK1,sK5,X0_52) = k7_relat_1(sK5,X0_52) ),
% 11.62/1.99      inference(global_propositional_subsumption,[status(thm)],[c_3456,c_44]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_16,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.62/1.99      inference(cnf_transformation,[],[f86]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_19,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_18,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_17,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_186,plain,
% 11.62/1.99      ( ~ v1_funct_1(X3)
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.62/1.99      inference(global_propositional_subsumption,
% 11.62/1.99                [status(thm)],
% 11.62/1.99                [c_16,c_19,c_18,c_17]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_187,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.62/1.99      inference(renaming,[status(thm)],[c_186]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_877,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0_52,X1_52,X2_52)
% 11.62/1.99      | ~ v1_funct_2(X3_52,X4_52,X2_52)
% 11.62/1.99      | ~ m1_subset_1(X4_52,k1_zfmisc_1(X5_52))
% 11.62/1.99      | ~ m1_subset_1(X1_52,k1_zfmisc_1(X5_52))
% 11.62/1.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 11.62/1.99      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X2_52)))
% 11.62/1.99      | ~ v1_funct_1(X0_52)
% 11.62/1.99      | ~ v1_funct_1(X3_52)
% 11.62/1.99      | v1_xboole_0(X1_52)
% 11.62/1.99      | v1_xboole_0(X2_52)
% 11.62/1.99      | v1_xboole_0(X4_52)
% 11.62/1.99      | v1_xboole_0(X5_52)
% 11.62/1.99      | k2_partfun1(X1_52,X2_52,X0_52,k9_subset_1(X5_52,X4_52,X1_52)) != k2_partfun1(X4_52,X2_52,X3_52,k9_subset_1(X5_52,X4_52,X1_52))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5_52,X4_52,X1_52),X2_52,k1_tmap_1(X5_52,X2_52,X4_52,X1_52,X3_52,X0_52),X4_52) = X3_52 ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_187]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1668,plain,
% 11.62/1.99      ( k2_partfun1(X0_52,X1_52,X2_52,k9_subset_1(X3_52,X4_52,X0_52)) != k2_partfun1(X4_52,X1_52,X5_52,k9_subset_1(X3_52,X4_52,X0_52))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X3_52,X4_52,X0_52),X1_52,k1_tmap_1(X3_52,X1_52,X4_52,X0_52,X5_52,X2_52),X4_52) = X5_52
% 11.62/1.99      | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
% 11.62/1.99      | v1_funct_2(X5_52,X4_52,X1_52) != iProver_top
% 11.62/1.99      | m1_subset_1(X4_52,k1_zfmisc_1(X3_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(X0_52,k1_zfmisc_1(X3_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 11.62/1.99      | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X1_52))) != iProver_top
% 11.62/1.99      | v1_funct_1(X2_52) != iProver_top
% 11.62/1.99      | v1_funct_1(X5_52) != iProver_top
% 11.62/1.99      | v1_xboole_0(X3_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(X1_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(X4_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(X0_52) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_877]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_4981,plain,
% 11.62/1.99      ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),X0_52) = X1_52
% 11.62/1.99      | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
% 11.62/1.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.62/1.99      | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
% 11.62/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/1.99      | v1_funct_1(X1_52) != iProver_top
% 11.62/1.99      | v1_funct_1(sK5) != iProver_top
% 11.62/1.99      | v1_xboole_0(X0_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(X2_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(sK1) = iProver_top
% 11.62/1.99      | v1_xboole_0(sK3) = iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_3534,c_1668]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_32,negated_conjecture,
% 11.62/1.99      ( ~ v1_xboole_0(sK1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_35,plain,
% 11.62/1.99      ( v1_xboole_0(sK1) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_29,negated_conjecture,
% 11.62/1.99      ( ~ v1_xboole_0(sK3) ),
% 11.62/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_38,plain,
% 11.62/1.99      ( v1_xboole_0(sK3) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_22,negated_conjecture,
% 11.62/1.99      ( v1_funct_2(sK5,sK3,sK1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_45,plain,
% 11.62/1.99      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_46,plain,
% 11.62/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5771,plain,
% 11.62/1.99      ( v1_funct_1(X1_52) != iProver_top
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/1.99      | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
% 11.62/1.99      | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),X0_52) = X1_52
% 11.62/1.99      | k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
% 11.62/1.99      | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
% 11.62/1.99      | v1_xboole_0(X0_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(X2_52) = iProver_top ),
% 11.62/1.99      inference(global_propositional_subsumption,
% 11.62/1.99                [status(thm)],
% 11.62/1.99                [c_4981,c_35,c_38,c_44,c_45,c_46]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5772,plain,
% 11.62/1.99      ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),X0_52) = X1_52
% 11.62/1.99      | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
% 11.62/1.99      | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/1.99      | v1_funct_1(X1_52) != iProver_top
% 11.62/1.99      | v1_xboole_0(X2_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(X0_52) = iProver_top ),
% 11.62/1.99      inference(renaming,[status(thm)],[c_5771]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5778,plain,
% 11.62/1.99      ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
% 11.62/1.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/1.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/1.99      | v1_funct_1(sK4) != iProver_top
% 11.62/1.99      | v1_xboole_0(X0_52) = iProver_top
% 11.62/1.99      | v1_xboole_0(sK2) = iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_3577,c_5772]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_31,negated_conjecture,
% 11.62/1.99      ( ~ v1_xboole_0(sK2) ),
% 11.62/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_36,plain,
% 11.62/1.99      ( v1_xboole_0(sK2) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_25,negated_conjecture,
% 11.62/1.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_42,plain,
% 11.62/1.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_43,plain,
% 11.62/1.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5892,plain,
% 11.62/1.99      ( v1_xboole_0(X0_52) = iProver_top
% 11.62/1.99      | k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top ),
% 11.62/1.99      inference(global_propositional_subsumption,
% 11.62/1.99                [status(thm)],
% 11.62/1.99                [c_5778,c_36,c_41,c_42,c_43]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5893,plain,
% 11.62/1.99      ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/1.99      | v1_xboole_0(X0_52) = iProver_top ),
% 11.62/1.99      inference(renaming,[status(thm)],[c_5892]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5898,plain,
% 11.62/1.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_2323,c_5893]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_10,plain,
% 11.62/1.99      ( ~ r1_subset_1(X0,X1)
% 11.62/1.99      | r1_xboole_0(X0,X1)
% 11.62/1.99      | v1_xboole_0(X0)
% 11.62/1.99      | v1_xboole_0(X1) ),
% 11.62/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_27,negated_conjecture,
% 11.62/1.99      ( r1_subset_1(sK2,sK3) ),
% 11.62/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_465,plain,
% 11.62/1.99      ( r1_xboole_0(X0,X1)
% 11.62/1.99      | v1_xboole_0(X0)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | sK3 != X1
% 11.62/1.99      | sK2 != X0 ),
% 11.62/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_466,plain,
% 11.62/1.99      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 11.62/1.99      inference(unflattening,[status(thm)],[c_465]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_468,plain,
% 11.62/1.99      ( r1_xboole_0(sK2,sK3) ),
% 11.62/1.99      inference(global_propositional_subsumption,
% 11.62/1.99                [status(thm)],
% 11.62/1.99                [c_466,c_31,c_29]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_874,plain,
% 11.62/1.99      ( r1_xboole_0(sK2,sK3) ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_468]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1671,plain,
% 11.62/1.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_874]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1,plain,
% 11.62/1.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_903,plain,
% 11.62/1.99      ( ~ r1_xboole_0(X0_52,X1_52) | k3_xboole_0(X0_52,X1_52) = k1_xboole_0 ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_1]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1643,plain,
% 11.62/1.99      ( k3_xboole_0(X0_52,X1_52) = k1_xboole_0
% 11.62/1.99      | r1_xboole_0(X0_52,X1_52) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_903]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_2682,plain,
% 11.62/1.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.62/1.99      inference(superposition,[status(thm)],[c_1671,c_1643]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5899,plain,
% 11.62/1.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/1.99      inference(light_normalisation,[status(thm)],[c_5898,c_2682]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5900,plain,
% 11.62/1.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/1.99      inference(demodulation,[status(thm)],[c_5899,c_2323]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5901,plain,
% 11.62/1.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 11.62/1.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/1.99      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/1.99      inference(light_normalisation,[status(thm)],[c_5900,c_2682]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_33,negated_conjecture,
% 11.62/1.99      ( ~ v1_xboole_0(sK0) ),
% 11.62/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_34,plain,
% 11.62/1.99      ( v1_xboole_0(sK0) != iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_30,negated_conjecture,
% 11.62/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 11.62/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_37,plain,
% 11.62/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_39,plain,
% 11.62/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.62/1.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_5902,plain,
% 11.62/1.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.62/1.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.62/1.99      | v1_xboole_0(sK0)
% 11.62/1.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/1.99      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.62/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_5901]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_15,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.62/1.99      inference(cnf_transformation,[],[f85]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_193,plain,
% 11.62/1.99      ( ~ v1_funct_1(X3)
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.62/1.99      inference(global_propositional_subsumption,
% 11.62/1.99                [status(thm)],
% 11.62/1.99                [c_15,c_19,c_18,c_17]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_194,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/1.99      | ~ v1_funct_2(X3,X4,X2)
% 11.62/1.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/1.99      | ~ v1_funct_1(X0)
% 11.62/1.99      | ~ v1_funct_1(X3)
% 11.62/1.99      | v1_xboole_0(X1)
% 11.62/1.99      | v1_xboole_0(X2)
% 11.62/1.99      | v1_xboole_0(X4)
% 11.62/1.99      | v1_xboole_0(X5)
% 11.62/1.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.62/1.99      inference(renaming,[status(thm)],[c_193]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_876,plain,
% 11.62/1.99      ( ~ v1_funct_2(X0_52,X1_52,X2_52)
% 11.62/1.99      | ~ v1_funct_2(X3_52,X4_52,X2_52)
% 11.62/1.99      | ~ m1_subset_1(X4_52,k1_zfmisc_1(X5_52))
% 11.62/1.99      | ~ m1_subset_1(X1_52,k1_zfmisc_1(X5_52))
% 11.62/1.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 11.62/1.99      | ~ m1_subset_1(X3_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X2_52)))
% 11.62/1.99      | ~ v1_funct_1(X0_52)
% 11.62/1.99      | ~ v1_funct_1(X3_52)
% 11.62/1.99      | v1_xboole_0(X1_52)
% 11.62/1.99      | v1_xboole_0(X2_52)
% 11.62/1.99      | v1_xboole_0(X4_52)
% 11.62/1.99      | v1_xboole_0(X5_52)
% 11.62/1.99      | k2_partfun1(X1_52,X2_52,X0_52,k9_subset_1(X5_52,X4_52,X1_52)) != k2_partfun1(X4_52,X2_52,X3_52,k9_subset_1(X5_52,X4_52,X1_52))
% 11.62/1.99      | k2_partfun1(k4_subset_1(X5_52,X4_52,X1_52),X2_52,k1_tmap_1(X5_52,X2_52,X4_52,X1_52,X3_52,X0_52),X1_52) = X0_52 ),
% 11.62/1.99      inference(subtyping,[status(esa)],[c_194]) ).
% 11.62/1.99  
% 11.62/1.99  cnf(c_1669,plain,
% 11.62/1.99      ( k2_partfun1(X0_52,X1_52,X2_52,k9_subset_1(X3_52,X4_52,X0_52)) != k2_partfun1(X4_52,X1_52,X5_52,k9_subset_1(X3_52,X4_52,X0_52))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X3_52,X4_52,X0_52),X1_52,k1_tmap_1(X3_52,X1_52,X4_52,X0_52,X5_52,X2_52),X0_52) = X2_52
% 11.62/2.00      | v1_funct_2(X2_52,X0_52,X1_52) != iProver_top
% 11.62/2.00      | v1_funct_2(X5_52,X4_52,X1_52) != iProver_top
% 11.62/2.00      | m1_subset_1(X4_52,k1_zfmisc_1(X3_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(X3_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(X2_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 11.62/2.00      | m1_subset_1(X5_52,k1_zfmisc_1(k2_zfmisc_1(X4_52,X1_52))) != iProver_top
% 11.62/2.00      | v1_funct_1(X2_52) != iProver_top
% 11.62/2.00      | v1_funct_1(X5_52) != iProver_top
% 11.62/2.00      | v1_xboole_0(X3_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(X1_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(X4_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(X0_52) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_876]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6031,plain,
% 11.62/2.00      ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),sK3) = sK5
% 11.62/2.00      | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
% 11.62/2.00      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/2.00      | v1_funct_1(X1_52) != iProver_top
% 11.62/2.00      | v1_funct_1(sK5) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(X2_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK1) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK3) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_3534,c_1669]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7315,plain,
% 11.62/2.00      ( v1_funct_1(X1_52) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/2.00      | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),sK3) = sK5
% 11.62/2.00      | k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
% 11.62/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(X2_52) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_6031,c_35,c_38,c_44,c_45,c_46]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7316,plain,
% 11.62/2.00      ( k2_partfun1(X0_52,sK1,X1_52,k9_subset_1(X2_52,X0_52,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_52,X0_52,sK3))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2_52,X0_52,sK3),sK1,k1_tmap_1(X2_52,sK1,X0_52,sK3,X1_52,sK5),sK3) = sK5
% 11.62/2.00      | v1_funct_2(X1_52,X0_52,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_52,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2_52)) != iProver_top
% 11.62/2.00      | v1_funct_1(X1_52) != iProver_top
% 11.62/2.00      | v1_xboole_0(X2_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(X0_52) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_7315]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7322,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
% 11.62/2.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0_52) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_3577,c_7316]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7382,plain,
% 11.62/2.00      ( v1_xboole_0(X0_52) = iProver_top
% 11.62/2.00      | k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_7322,c_36,c_41,c_42,c_43]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7383,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(X0_52,sK2,sK3),sK1,k1_tmap_1(X0_52,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0_52,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_52,sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0_52)) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0_52) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_7382]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7388,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2323,c_7383]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12,plain,
% 11.62/2.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.62/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6,plain,
% 11.62/2.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_444,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ v1_relat_1(X0)
% 11.62/2.00      | k7_relat_1(X0,X1) = X0 ),
% 11.62/2.00      inference(resolution,[status(thm)],[c_12,c_6]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_11,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_448,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | k7_relat_1(X0,X1) = X0 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_444,c_12,c_11,c_6]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_875,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 11.62/2.00      | k7_relat_1(X0_52,X1_52) = X0_52 ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_448]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1670,plain,
% 11.62/2.00      ( k7_relat_1(X0_52,X1_52) = X0_52
% 11.62/2.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_875]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6500,plain,
% 11.62/2.00      ( k7_relat_1(sK5,sK3) = sK5 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1656,c_1670]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_896,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52)))
% 11.62/2.00      | v1_relat_1(X0_52) ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_11]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1650,plain,
% 11.62/2.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X1_52,X2_52))) != iProver_top
% 11.62/2.00      | v1_relat_1(X0_52) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_896]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2608,plain,
% 11.62/2.00      ( v1_relat_1(sK5) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1656,c_1650]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2,plain,
% 11.62/2.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_902,plain,
% 11.62/2.00      ( ~ r1_xboole_0(X0_52,X1_52) | r1_xboole_0(X1_52,X0_52) ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_2]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1644,plain,
% 11.62/2.00      ( r1_xboole_0(X0_52,X1_52) != iProver_top
% 11.62/2.00      | r1_xboole_0(X1_52,X0_52) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_902]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2684,plain,
% 11.62/2.00      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1671,c_1644]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5,plain,
% 11.62/2.00      ( ~ r1_xboole_0(X0,X1)
% 11.62/2.00      | ~ v1_relat_1(X2)
% 11.62/2.00      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_899,plain,
% 11.62/2.00      ( ~ r1_xboole_0(X0_52,X1_52)
% 11.62/2.00      | ~ v1_relat_1(X2_52)
% 11.62/2.00      | k7_relat_1(k7_relat_1(X2_52,X0_52),X1_52) = k1_xboole_0 ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_5]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1647,plain,
% 11.62/2.00      ( k7_relat_1(k7_relat_1(X0_52,X1_52),X2_52) = k1_xboole_0
% 11.62/2.00      | r1_xboole_0(X1_52,X2_52) != iProver_top
% 11.62/2.00      | v1_relat_1(X0_52) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_899]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3511,plain,
% 11.62/2.00      ( k7_relat_1(k7_relat_1(X0_52,sK3),sK2) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(X0_52) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2684,c_1647]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3718,plain,
% 11.62/2.00      ( k7_relat_1(k7_relat_1(sK5,sK3),sK2) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2608,c_3511]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(X0),X1)
% 11.62/2.00      | ~ v1_relat_1(X0)
% 11.62/2.00      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_897,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(X0_52),X1_52)
% 11.62/2.00      | ~ v1_relat_1(X0_52)
% 11.62/2.00      | k7_relat_1(X0_52,X1_52) != k1_xboole_0 ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_8]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1649,plain,
% 11.62/2.00      ( k7_relat_1(X0_52,X1_52) != k1_xboole_0
% 11.62/2.00      | r1_xboole_0(k1_relat_1(X0_52),X1_52) = iProver_top
% 11.62/2.00      | v1_relat_1(X0_52) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_897]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3745,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK5,sK3)),sK2) = iProver_top
% 11.62/2.00      | v1_relat_1(k7_relat_1(sK5,sK3)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_3718,c_1649]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3891,plain,
% 11.62/2.00      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK5,sK3)),sK2) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(k7_relat_1(sK5,sK3)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_3745,c_1643]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6506,plain,
% 11.62/2.00      ( k3_xboole_0(k1_relat_1(sK5),sK2) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(sK5) != iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_6500,c_3891]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6643,plain,
% 11.62/2.00      ( k3_xboole_0(k1_relat_1(sK5),sK2) = k1_xboole_0 ),
% 11.62/2.00      inference(global_propositional_subsumption,[status(thm)],[c_6506,c_2608]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0)
% 11.62/2.00      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_900,plain,
% 11.62/2.00      ( ~ v1_relat_1(X0_52)
% 11.62/2.00      | k7_relat_1(X0_52,k3_xboole_0(k1_relat_1(X0_52),X1_52)) = k7_relat_1(X0_52,X1_52) ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_4]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1646,plain,
% 11.62/2.00      ( k7_relat_1(X0_52,k3_xboole_0(k1_relat_1(X0_52),X1_52)) = k7_relat_1(X0_52,X1_52)
% 11.62/2.00      | v1_relat_1(X0_52) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_900]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2852,plain,
% 11.62/2.00      ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_52)) = k7_relat_1(sK5,X0_52) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2608,c_1646]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6647,plain,
% 11.62/2.00      ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_6643,c_2852]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6509,plain,
% 11.62/2.00      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_6500,c_3718]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6650,plain,
% 11.62/2.00      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_6647,c_6509]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7389,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_7388,c_2682,c_6650]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7390,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_7389,c_2323]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6501,plain,
% 11.62/2.00      ( k7_relat_1(sK4,sK2) = sK4 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1659,c_1670]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2609,plain,
% 11.62/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1659,c_1650]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3510,plain,
% 11.62/2.00      ( k7_relat_1(k7_relat_1(X0_52,sK2),sK3) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(X0_52) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1671,c_1647]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3582,plain,
% 11.62/2.00      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2609,c_3510]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3667,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK4,sK2)),sK3) = iProver_top
% 11.62/2.00      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_3582,c_1649]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3881,plain,
% 11.62/2.00      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK4,sK2)),sK3) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_3667,c_1643]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6555,plain,
% 11.62/2.00      ( k3_xboole_0(k1_relat_1(sK4),sK3) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(sK4) != iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_6501,c_3881]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6697,plain,
% 11.62/2.00      ( k3_xboole_0(k1_relat_1(sK4),sK3) = k1_xboole_0 ),
% 11.62/2.00      inference(global_propositional_subsumption,[status(thm)],[c_6555,c_2609]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2855,plain,
% 11.62/2.00      ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_52)) = k7_relat_1(sK4,X0_52) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2609,c_1646]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6701,plain,
% 11.62/2.00      ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_6697,c_2855]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6558,plain,
% 11.62/2.00      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_6501,c_3582]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6704,plain,
% 11.62/2.00      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_6701,c_6558]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7391,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k1_xboole_0 != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_7390,c_2682,c_6704]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7392,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(equality_resolution_simp,[status(thm)],[c_7391]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20,negated_conjecture,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_890,negated_conjecture,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.62/2.00      inference(subtyping,[status(esa)],[c_20]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2527,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_2323,c_890]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3243,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_2682,c_2527]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3537,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_3534,c_3243]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3716,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_3537,c_3577]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_13254,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_6650,c_3716]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_13255,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_13254,c_6704]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_13256,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 11.62/2.00      inference(equality_resolution_simp,[status(thm)],[c_13255]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15506,plain,
% 11.62/2.00      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5901,c_33,c_34,c_30,c_37,c_28,c_39,c_5902,c_7392,c_13256]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15508,plain,
% 11.62/2.00      ( k1_xboole_0 != k1_xboole_0 ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_15506,c_6650,c_6704]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15509,plain,
% 11.62/2.00      ( $false ),
% 11.62/2.00      inference(equality_resolution_simp,[status(thm)],[c_15508]) ).
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  ------                               Statistics
% 11.62/2.00  
% 11.62/2.00  ------ General
% 11.62/2.00  
% 11.62/2.00  abstr_ref_over_cycles:                  0
% 11.62/2.00  abstr_ref_under_cycles:                 0
% 11.62/2.00  gc_basic_clause_elim:                   0
% 11.62/2.00  forced_gc_time:                         0
% 11.62/2.00  parsing_time:                           0.017
% 11.62/2.00  unif_index_cands_time:                  0.
% 11.62/2.00  unif_index_add_time:                    0.
% 11.62/2.00  orderings_time:                         0.
% 11.62/2.00  out_proof_time:                         0.019
% 11.62/2.00  total_time:                             1.044
% 11.62/2.00  num_of_symbols:                         57
% 11.62/2.00  num_of_terms:                           41760
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing
% 11.62/2.00  
% 11.62/2.00  num_of_splits:                          0
% 11.62/2.00  num_of_split_atoms:                     0
% 11.62/2.00  num_of_reused_defs:                     0
% 11.62/2.00  num_eq_ax_congr_red:                    12
% 11.62/2.00  num_of_sem_filtered_clauses:            1
% 11.62/2.00  num_of_subtypes:                        2
% 11.62/2.00  monotx_restored_types:                  0
% 11.62/2.00  sat_num_of_epr_types:                   0
% 11.62/2.00  sat_num_of_non_cyclic_types:            0
% 11.62/2.00  sat_guarded_non_collapsed_types:        1
% 11.62/2.00  num_pure_diseq_elim:                    0
% 11.62/2.00  simp_replaced_by:                       0
% 11.62/2.00  res_preprocessed:                       160
% 11.62/2.00  prep_upred:                             0
% 11.62/2.00  prep_unflattend:                        4
% 11.62/2.00  smt_new_axioms:                         0
% 11.62/2.00  pred_elim_cands:                        6
% 11.62/2.00  pred_elim:                              2
% 11.62/2.00  pred_elim_cl:                           3
% 11.62/2.00  pred_elim_cycles:                       4
% 11.62/2.00  merged_defs:                            8
% 11.62/2.00  merged_defs_ncl:                        0
% 11.62/2.00  bin_hyper_res:                          8
% 11.62/2.00  prep_cycles:                            4
% 11.62/2.00  pred_elim_time:                         0.004
% 11.62/2.00  splitting_time:                         0.
% 11.62/2.00  sem_filter_time:                        0.
% 11.62/2.00  monotx_time:                            0.
% 11.62/2.00  subtype_inf_time:                       0.001
% 11.62/2.00  
% 11.62/2.00  ------ Problem properties
% 11.62/2.00  
% 11.62/2.00  clauses:                                31
% 11.62/2.00  conjectures:                            13
% 11.62/2.00  epr:                                    10
% 11.62/2.00  horn:                                   25
% 11.62/2.00  ground:                                 14
% 11.62/2.00  unary:                                  13
% 11.62/2.00  binary:                                 7
% 11.62/2.00  lits:                                   126
% 11.62/2.00  lits_eq:                                18
% 11.62/2.00  fd_pure:                                0
% 11.62/2.00  fd_pseudo:                              0
% 11.62/2.00  fd_cond:                                0
% 11.62/2.00  fd_pseudo_cond:                         0
% 11.62/2.00  ac_symbols:                             0
% 11.62/2.00  
% 11.62/2.00  ------ Propositional Solver
% 11.62/2.00  
% 11.62/2.00  prop_solver_calls:                      31
% 11.62/2.00  prop_fast_solver_calls:                 3614
% 11.62/2.00  smt_solver_calls:                       0
% 11.62/2.00  smt_fast_solver_calls:                  0
% 11.62/2.00  prop_num_of_clauses:                    8488
% 11.62/2.00  prop_preprocess_simplified:             16140
% 11.62/2.00  prop_fo_subsumed:                       211
% 11.62/2.00  prop_solver_time:                       0.
% 11.62/2.00  smt_solver_time:                        0.
% 11.62/2.00  smt_fast_solver_time:                   0.
% 11.62/2.00  prop_fast_solver_time:                  0.
% 11.62/2.00  prop_unsat_core_time:                   0.
% 11.62/2.00  
% 11.62/2.00  ------ QBF
% 11.62/2.00  
% 11.62/2.00  qbf_q_res:                              0
% 11.62/2.00  qbf_num_tautologies:                    0
% 11.62/2.00  qbf_prep_cycles:                        0
% 11.62/2.00  
% 11.62/2.00  ------ BMC1
% 11.62/2.00  
% 11.62/2.00  bmc1_current_bound:                     -1
% 11.62/2.00  bmc1_last_solved_bound:                 -1
% 11.62/2.00  bmc1_unsat_core_size:                   -1
% 11.62/2.00  bmc1_unsat_core_parents_size:           -1
% 11.62/2.00  bmc1_merge_next_fun:                    0
% 11.62/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.62/2.00  
% 11.62/2.00  ------ Instantiation
% 11.62/2.00  
% 11.62/2.00  inst_num_of_clauses:                    2030
% 11.62/2.00  inst_num_in_passive:                    49
% 11.62/2.00  inst_num_in_active:                     1287
% 11.62/2.00  inst_num_in_unprocessed:                694
% 11.62/2.00  inst_num_of_loops:                      1410
% 11.62/2.00  inst_num_of_learning_restarts:          0
% 11.62/2.00  inst_num_moves_active_passive:          120
% 11.62/2.00  inst_lit_activity:                      0
% 11.62/2.00  inst_lit_activity_moves:                1
% 11.62/2.00  inst_num_tautologies:                   0
% 11.62/2.00  inst_num_prop_implied:                  0
% 11.62/2.00  inst_num_existing_simplified:           0
% 11.62/2.00  inst_num_eq_res_simplified:             0
% 11.62/2.00  inst_num_child_elim:                    0
% 11.62/2.00  inst_num_of_dismatching_blockings:      366
% 11.62/2.00  inst_num_of_non_proper_insts:           2306
% 11.62/2.00  inst_num_of_duplicates:                 0
% 11.62/2.00  inst_inst_num_from_inst_to_res:         0
% 11.62/2.00  inst_dismatching_checking_time:         0.
% 11.62/2.00  
% 11.62/2.00  ------ Resolution
% 11.62/2.00  
% 11.62/2.00  res_num_of_clauses:                     0
% 11.62/2.00  res_num_in_passive:                     0
% 11.62/2.00  res_num_in_active:                      0
% 11.62/2.00  res_num_of_loops:                       164
% 11.62/2.00  res_forward_subset_subsumed:            45
% 11.62/2.00  res_backward_subset_subsumed:           0
% 11.62/2.00  res_forward_subsumed:                   0
% 11.62/2.00  res_backward_subsumed:                  0
% 11.62/2.00  res_forward_subsumption_resolution:     0
% 11.62/2.00  res_backward_subsumption_resolution:    0
% 11.62/2.00  res_clause_to_clause_subsumption:       1052
% 11.62/2.00  res_orphan_elimination:                 0
% 11.62/2.00  res_tautology_del:                      28
% 11.62/2.00  res_num_eq_res_simplified:              0
% 11.62/2.00  res_num_sel_changes:                    0
% 11.62/2.00  res_moves_from_active_to_pass:          0
% 11.62/2.00  
% 11.62/2.00  ------ Superposition
% 11.62/2.00  
% 11.62/2.00  sup_time_total:                         0.
% 11.62/2.00  sup_time_generating:                    0.
% 11.62/2.00  sup_time_sim_full:                      0.
% 11.62/2.00  sup_time_sim_immed:                     0.
% 11.62/2.00  
% 11.62/2.00  sup_num_of_clauses:                     351
% 11.62/2.00  sup_num_in_active:                      260
% 11.62/2.00  sup_num_in_passive:                     91
% 11.62/2.00  sup_num_of_loops:                       280
% 11.62/2.00  sup_fw_superposition:                   239
% 11.62/2.00  sup_bw_superposition:                   238
% 11.62/2.00  sup_immediate_simplified:               225
% 11.62/2.00  sup_given_eliminated:                   0
% 11.62/2.00  comparisons_done:                       0
% 11.62/2.00  comparisons_avoided:                    0
% 11.62/2.00  
% 11.62/2.00  ------ Simplifications
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  sim_fw_subset_subsumed:                 24
% 11.62/2.00  sim_bw_subset_subsumed:                 4
% 11.62/2.00  sim_fw_subsumed:                        24
% 11.62/2.00  sim_bw_subsumed:                        8
% 11.62/2.00  sim_fw_subsumption_res:                 0
% 11.62/2.00  sim_bw_subsumption_res:                 0
% 11.62/2.00  sim_tautology_del:                      0
% 11.62/2.00  sim_eq_tautology_del:                   11
% 11.62/2.00  sim_eq_res_simp:                        5
% 11.62/2.00  sim_fw_demodulated:                     65
% 11.62/2.00  sim_bw_demodulated:                     20
% 11.62/2.00  sim_light_normalised:                   143
% 11.62/2.00  sim_joinable_taut:                      0
% 11.62/2.00  sim_joinable_simp:                      0
% 11.62/2.00  sim_ac_normalised:                      0
% 11.62/2.00  sim_smt_subsumption:                    0
% 11.62/2.00  
%------------------------------------------------------------------------------
