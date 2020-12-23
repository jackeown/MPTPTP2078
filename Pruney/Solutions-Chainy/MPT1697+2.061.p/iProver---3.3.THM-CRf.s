%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:36 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  234 (1901 expanded)
%              Number of clauses        :  137 ( 584 expanded)
%              Number of leaves         :   24 ( 585 expanded)
%              Depth                    :   22
%              Number of atoms          : 1145 (17032 expanded)
%              Number of equality atoms :  436 (4284 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f41,f58,f57,f56,f55,f54,f53])).

fof(f96,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f100,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f98,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f101,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
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
    inference(equality_resolution,[],[f86])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f102,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f93,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,(
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
    inference(equality_resolution,[],[f85])).

fof(f104,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2081,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2098,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4201,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_2098])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_323,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_323])).

cnf(c_411,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_324])).

cnf(c_2073,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_17792,plain,
    ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_4201,c_2073])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2084,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2092,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5122,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_2092])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_52,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5407,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5122,c_52])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2087,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5121,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2092])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_55,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5241,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5121,c_55])).

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
    inference(cnf_transformation,[],[f111])).

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
    inference(cnf_transformation,[],[f88])).

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
    inference(cnf_transformation,[],[f89])).

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
    inference(cnf_transformation,[],[f90])).

cnf(c_242,plain,
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

cnf(c_243,plain,
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
    inference(renaming,[status(thm)],[c_242])).

cnf(c_2074,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
    | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X5,X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_5246,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5241,c_2074])).

cnf(c_43,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_49,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_56,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_57,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6679,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5246,c_46,c_49,c_55,c_56,c_57])).

cnf(c_6680,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6679])).

cnf(c_6686,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5407,c_6680])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_53,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_54,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6691,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6686,c_47,c_52,c_53,c_54])).

cnf(c_6692,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6691])).

cnf(c_20799,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17792,c_6692])).

cnf(c_21,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_38,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_555,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_556,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_555])).

cnf(c_558,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_556,c_42,c_40])).

cnf(c_2072,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2104,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3998,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2072,c_2104])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2093,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4259,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_2093])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2101,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2099,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_23,c_17])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_23,c_22,c_17])).

cnf(c_2071,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_3296,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2071])).

cnf(c_4253,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_3296])).

cnf(c_4472,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2101,c_4253])).

cnf(c_19,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2094,plain,
    ( k7_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5050,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4472,c_2094])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2097,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3375,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2097])).

cnf(c_6882,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5050,c_3375])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2103,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6889,plain,
    ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6882,c_2103])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2095,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7341,plain,
    ( k7_relat_1(X0,k1_relat_1(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6889,c_2095])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2100,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_585,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_14])).

cnf(c_589,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_22])).

cnf(c_590,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_589])).

cnf(c_2070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_4210,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2099,c_2070])).

cnf(c_8297,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_4210])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2102,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4696,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2102])).

cnf(c_8510,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8297,c_4696])).

cnf(c_10233,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7341,c_8510])).

cnf(c_10237,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4259,c_10233])).

cnf(c_20805,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20799,c_3998,c_10237])).

cnf(c_20806,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20805,c_17792])).

cnf(c_4260,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2084,c_2093])).

cnf(c_10238,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4260,c_10233])).

cnf(c_20807,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20806,c_3998,c_10238])).

cnf(c_20808,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_20807])).

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
    inference(cnf_transformation,[],[f112])).

cnf(c_235,plain,
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

cnf(c_236,plain,
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
    inference(renaming,[status(thm)],[c_235])).

cnf(c_2075,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
    | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X5,X4,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_236])).

cnf(c_5245,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5241,c_2075])).

cnf(c_6451,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5245,c_46,c_49,c_55,c_56,c_57])).

cnf(c_6452,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6451])).

cnf(c_6458,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5407,c_6452])).

cnf(c_6576,plain,
    ( v1_xboole_0(X0) = iProver_top
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6458,c_47,c_52,c_53,c_54])).

cnf(c_6577,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6576])).

cnf(c_20800,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17792,c_6577])).

cnf(c_20801,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20800,c_3998,c_10237])).

cnf(c_20802,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20801,c_17792])).

cnf(c_20803,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20802,c_3998,c_10238])).

cnf(c_20804,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_20803])).

cnf(c_31,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5244,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_5241,c_31])).

cnf(c_5410,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_5407,c_5244])).

cnf(c_20784,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_17792,c_5410])).

cnf(c_20785,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_20784,c_3998,c_10237,c_10238])).

cnf(c_20786,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_20785])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20808,c_20804,c_20786,c_50,c_48,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:05:52 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running in FOF mode
% 11.62/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.62/2.00  
% 11.62/2.00  ------  iProver source info
% 11.62/2.00  
% 11.62/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.62/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.62/2.00  git: non_committed_changes: false
% 11.62/2.00  git: last_make_outside_of_git: false
% 11.62/2.00  
% 11.62/2.00  ------ 
% 11.62/2.00  
% 11.62/2.00  ------ Input Options
% 11.62/2.00  
% 11.62/2.00  --out_options                           all
% 11.62/2.00  --tptp_safe_out                         true
% 11.62/2.00  --problem_path                          ""
% 11.62/2.00  --include_path                          ""
% 11.62/2.00  --clausifier                            res/vclausify_rel
% 11.62/2.00  --clausifier_options                    ""
% 11.62/2.00  --stdin                                 false
% 11.62/2.00  --stats_out                             all
% 11.62/2.00  
% 11.62/2.00  ------ General Options
% 11.62/2.00  
% 11.62/2.00  --fof                                   false
% 11.62/2.00  --time_out_real                         305.
% 11.62/2.00  --time_out_virtual                      -1.
% 11.62/2.00  --symbol_type_check                     false
% 11.62/2.00  --clausify_out                          false
% 11.62/2.00  --sig_cnt_out                           false
% 11.62/2.00  --trig_cnt_out                          false
% 11.62/2.00  --trig_cnt_out_tolerance                1.
% 11.62/2.00  --trig_cnt_out_sk_spl                   false
% 11.62/2.00  --abstr_cl_out                          false
% 11.62/2.00  
% 11.62/2.00  ------ Global Options
% 11.62/2.00  
% 11.62/2.00  --schedule                              default
% 11.62/2.00  --add_important_lit                     false
% 11.62/2.00  --prop_solver_per_cl                    1000
% 11.62/2.00  --min_unsat_core                        false
% 11.62/2.00  --soft_assumptions                      false
% 11.62/2.00  --soft_lemma_size                       3
% 11.62/2.00  --prop_impl_unit_size                   0
% 11.62/2.00  --prop_impl_unit                        []
% 11.62/2.00  --share_sel_clauses                     true
% 11.62/2.00  --reset_solvers                         false
% 11.62/2.00  --bc_imp_inh                            [conj_cone]
% 11.62/2.00  --conj_cone_tolerance                   3.
% 11.62/2.00  --extra_neg_conj                        none
% 11.62/2.00  --large_theory_mode                     true
% 11.62/2.00  --prolific_symb_bound                   200
% 11.62/2.00  --lt_threshold                          2000
% 11.62/2.00  --clause_weak_htbl                      true
% 11.62/2.00  --gc_record_bc_elim                     false
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing Options
% 11.62/2.00  
% 11.62/2.00  --preprocessing_flag                    true
% 11.62/2.00  --time_out_prep_mult                    0.1
% 11.62/2.00  --splitting_mode                        input
% 11.62/2.00  --splitting_grd                         true
% 11.62/2.00  --splitting_cvd                         false
% 11.62/2.00  --splitting_cvd_svl                     false
% 11.62/2.00  --splitting_nvd                         32
% 11.62/2.00  --sub_typing                            true
% 11.62/2.00  --prep_gs_sim                           true
% 11.62/2.00  --prep_unflatten                        true
% 11.62/2.00  --prep_res_sim                          true
% 11.62/2.00  --prep_upred                            true
% 11.62/2.00  --prep_sem_filter                       exhaustive
% 11.62/2.00  --prep_sem_filter_out                   false
% 11.62/2.00  --pred_elim                             true
% 11.62/2.00  --res_sim_input                         true
% 11.62/2.00  --eq_ax_congr_red                       true
% 11.62/2.00  --pure_diseq_elim                       true
% 11.62/2.00  --brand_transform                       false
% 11.62/2.00  --non_eq_to_eq                          false
% 11.62/2.00  --prep_def_merge                        true
% 11.62/2.00  --prep_def_merge_prop_impl              false
% 11.62/2.00  --prep_def_merge_mbd                    true
% 11.62/2.00  --prep_def_merge_tr_red                 false
% 11.62/2.00  --prep_def_merge_tr_cl                  false
% 11.62/2.00  --smt_preprocessing                     true
% 11.62/2.00  --smt_ac_axioms                         fast
% 11.62/2.00  --preprocessed_out                      false
% 11.62/2.00  --preprocessed_stats                    false
% 11.62/2.00  
% 11.62/2.00  ------ Abstraction refinement Options
% 11.62/2.00  
% 11.62/2.00  --abstr_ref                             []
% 11.62/2.00  --abstr_ref_prep                        false
% 11.62/2.00  --abstr_ref_until_sat                   false
% 11.62/2.00  --abstr_ref_sig_restrict                funpre
% 11.62/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.62/2.00  --abstr_ref_under                       []
% 11.62/2.00  
% 11.62/2.00  ------ SAT Options
% 11.62/2.00  
% 11.62/2.00  --sat_mode                              false
% 11.62/2.00  --sat_fm_restart_options                ""
% 11.62/2.00  --sat_gr_def                            false
% 11.62/2.00  --sat_epr_types                         true
% 11.62/2.00  --sat_non_cyclic_types                  false
% 11.62/2.00  --sat_finite_models                     false
% 11.62/2.00  --sat_fm_lemmas                         false
% 11.62/2.00  --sat_fm_prep                           false
% 11.62/2.00  --sat_fm_uc_incr                        true
% 11.62/2.00  --sat_out_model                         small
% 11.62/2.00  --sat_out_clauses                       false
% 11.62/2.00  
% 11.62/2.00  ------ QBF Options
% 11.62/2.00  
% 11.62/2.00  --qbf_mode                              false
% 11.62/2.00  --qbf_elim_univ                         false
% 11.62/2.00  --qbf_dom_inst                          none
% 11.62/2.00  --qbf_dom_pre_inst                      false
% 11.62/2.00  --qbf_sk_in                             false
% 11.62/2.00  --qbf_pred_elim                         true
% 11.62/2.00  --qbf_split                             512
% 11.62/2.00  
% 11.62/2.00  ------ BMC1 Options
% 11.62/2.00  
% 11.62/2.00  --bmc1_incremental                      false
% 11.62/2.00  --bmc1_axioms                           reachable_all
% 11.62/2.00  --bmc1_min_bound                        0
% 11.62/2.00  --bmc1_max_bound                        -1
% 11.62/2.00  --bmc1_max_bound_default                -1
% 11.62/2.00  --bmc1_symbol_reachability              true
% 11.62/2.00  --bmc1_property_lemmas                  false
% 11.62/2.00  --bmc1_k_induction                      false
% 11.62/2.00  --bmc1_non_equiv_states                 false
% 11.62/2.00  --bmc1_deadlock                         false
% 11.62/2.00  --bmc1_ucm                              false
% 11.62/2.00  --bmc1_add_unsat_core                   none
% 11.62/2.00  --bmc1_unsat_core_children              false
% 11.62/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.62/2.00  --bmc1_out_stat                         full
% 11.62/2.00  --bmc1_ground_init                      false
% 11.62/2.00  --bmc1_pre_inst_next_state              false
% 11.62/2.00  --bmc1_pre_inst_state                   false
% 11.62/2.00  --bmc1_pre_inst_reach_state             false
% 11.62/2.00  --bmc1_out_unsat_core                   false
% 11.62/2.00  --bmc1_aig_witness_out                  false
% 11.62/2.00  --bmc1_verbose                          false
% 11.62/2.00  --bmc1_dump_clauses_tptp                false
% 11.62/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.62/2.00  --bmc1_dump_file                        -
% 11.62/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.62/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.62/2.00  --bmc1_ucm_extend_mode                  1
% 11.62/2.00  --bmc1_ucm_init_mode                    2
% 11.62/2.00  --bmc1_ucm_cone_mode                    none
% 11.62/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.62/2.00  --bmc1_ucm_relax_model                  4
% 11.62/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.62/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.62/2.00  --bmc1_ucm_layered_model                none
% 11.62/2.00  --bmc1_ucm_max_lemma_size               10
% 11.62/2.00  
% 11.62/2.00  ------ AIG Options
% 11.62/2.00  
% 11.62/2.00  --aig_mode                              false
% 11.62/2.00  
% 11.62/2.00  ------ Instantiation Options
% 11.62/2.00  
% 11.62/2.00  --instantiation_flag                    true
% 11.62/2.00  --inst_sos_flag                         true
% 11.62/2.00  --inst_sos_phase                        true
% 11.62/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.62/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.62/2.00  --inst_lit_sel_side                     num_symb
% 11.62/2.00  --inst_solver_per_active                1400
% 11.62/2.00  --inst_solver_calls_frac                1.
% 11.62/2.00  --inst_passive_queue_type               priority_queues
% 11.62/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.62/2.00  --inst_passive_queues_freq              [25;2]
% 11.62/2.00  --inst_dismatching                      true
% 11.62/2.00  --inst_eager_unprocessed_to_passive     true
% 11.62/2.00  --inst_prop_sim_given                   true
% 11.62/2.00  --inst_prop_sim_new                     false
% 11.62/2.00  --inst_subs_new                         false
% 11.62/2.00  --inst_eq_res_simp                      false
% 11.62/2.00  --inst_subs_given                       false
% 11.62/2.00  --inst_orphan_elimination               true
% 11.62/2.00  --inst_learning_loop_flag               true
% 11.62/2.00  --inst_learning_start                   3000
% 11.62/2.00  --inst_learning_factor                  2
% 11.62/2.00  --inst_start_prop_sim_after_learn       3
% 11.62/2.00  --inst_sel_renew                        solver
% 11.62/2.00  --inst_lit_activity_flag                true
% 11.62/2.00  --inst_restr_to_given                   false
% 11.62/2.00  --inst_activity_threshold               500
% 11.62/2.00  --inst_out_proof                        true
% 11.62/2.00  
% 11.62/2.00  ------ Resolution Options
% 11.62/2.00  
% 11.62/2.00  --resolution_flag                       true
% 11.62/2.00  --res_lit_sel                           adaptive
% 11.62/2.00  --res_lit_sel_side                      none
% 11.62/2.00  --res_ordering                          kbo
% 11.62/2.00  --res_to_prop_solver                    active
% 11.62/2.00  --res_prop_simpl_new                    false
% 11.62/2.00  --res_prop_simpl_given                  true
% 11.62/2.00  --res_passive_queue_type                priority_queues
% 11.62/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.62/2.00  --res_passive_queues_freq               [15;5]
% 11.62/2.00  --res_forward_subs                      full
% 11.62/2.00  --res_backward_subs                     full
% 11.62/2.00  --res_forward_subs_resolution           true
% 11.62/2.00  --res_backward_subs_resolution          true
% 11.62/2.00  --res_orphan_elimination                true
% 11.62/2.00  --res_time_limit                        2.
% 11.62/2.00  --res_out_proof                         true
% 11.62/2.00  
% 11.62/2.00  ------ Superposition Options
% 11.62/2.00  
% 11.62/2.00  --superposition_flag                    true
% 11.62/2.00  --sup_passive_queue_type                priority_queues
% 11.62/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.62/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.62/2.00  --demod_completeness_check              fast
% 11.62/2.00  --demod_use_ground                      true
% 11.62/2.00  --sup_to_prop_solver                    passive
% 11.62/2.00  --sup_prop_simpl_new                    true
% 11.62/2.00  --sup_prop_simpl_given                  true
% 11.62/2.00  --sup_fun_splitting                     true
% 11.62/2.00  --sup_smt_interval                      50000
% 11.62/2.00  
% 11.62/2.00  ------ Superposition Simplification Setup
% 11.62/2.00  
% 11.62/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.62/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.62/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.62/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.62/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.62/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.62/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.62/2.00  --sup_immed_triv                        [TrivRules]
% 11.62/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/2.00  --sup_immed_bw_main                     []
% 11.62/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.62/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.62/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/2.00  --sup_input_bw                          []
% 11.62/2.00  
% 11.62/2.00  ------ Combination Options
% 11.62/2.00  
% 11.62/2.00  --comb_res_mult                         3
% 11.62/2.00  --comb_sup_mult                         2
% 11.62/2.00  --comb_inst_mult                        10
% 11.62/2.00  
% 11.62/2.00  ------ Debug Options
% 11.62/2.00  
% 11.62/2.00  --dbg_backtrace                         false
% 11.62/2.00  --dbg_dump_prop_clauses                 false
% 11.62/2.00  --dbg_dump_prop_clauses_file            -
% 11.62/2.00  --dbg_out_stat                          false
% 11.62/2.00  ------ Parsing...
% 11.62/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/2.00  ------ Proving...
% 11.62/2.00  ------ Problem Properties 
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  clauses                                 41
% 11.62/2.00  conjectures                             13
% 11.62/2.00  EPR                                     13
% 11.62/2.00  Horn                                    34
% 11.62/2.00  unary                                   18
% 11.62/2.00  binary                                  9
% 11.62/2.00  lits                                    144
% 11.62/2.00  lits eq                                 24
% 11.62/2.00  fd_pure                                 0
% 11.62/2.00  fd_pseudo                               0
% 11.62/2.00  fd_cond                                 1
% 11.62/2.00  fd_pseudo_cond                          1
% 11.62/2.00  AC symbols                              0
% 11.62/2.00  
% 11.62/2.00  ------ Schedule dynamic 5 is on 
% 11.62/2.00  
% 11.62/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  ------ 
% 11.62/2.00  Current options:
% 11.62/2.00  ------ 
% 11.62/2.00  
% 11.62/2.00  ------ Input Options
% 11.62/2.00  
% 11.62/2.00  --out_options                           all
% 11.62/2.00  --tptp_safe_out                         true
% 11.62/2.00  --problem_path                          ""
% 11.62/2.00  --include_path                          ""
% 11.62/2.00  --clausifier                            res/vclausify_rel
% 11.62/2.00  --clausifier_options                    ""
% 11.62/2.00  --stdin                                 false
% 11.62/2.00  --stats_out                             all
% 11.62/2.00  
% 11.62/2.00  ------ General Options
% 11.62/2.00  
% 11.62/2.00  --fof                                   false
% 11.62/2.00  --time_out_real                         305.
% 11.62/2.00  --time_out_virtual                      -1.
% 11.62/2.00  --symbol_type_check                     false
% 11.62/2.00  --clausify_out                          false
% 11.62/2.00  --sig_cnt_out                           false
% 11.62/2.00  --trig_cnt_out                          false
% 11.62/2.00  --trig_cnt_out_tolerance                1.
% 11.62/2.00  --trig_cnt_out_sk_spl                   false
% 11.62/2.00  --abstr_cl_out                          false
% 11.62/2.00  
% 11.62/2.00  ------ Global Options
% 11.62/2.00  
% 11.62/2.00  --schedule                              default
% 11.62/2.00  --add_important_lit                     false
% 11.62/2.00  --prop_solver_per_cl                    1000
% 11.62/2.00  --min_unsat_core                        false
% 11.62/2.00  --soft_assumptions                      false
% 11.62/2.00  --soft_lemma_size                       3
% 11.62/2.00  --prop_impl_unit_size                   0
% 11.62/2.00  --prop_impl_unit                        []
% 11.62/2.00  --share_sel_clauses                     true
% 11.62/2.00  --reset_solvers                         false
% 11.62/2.00  --bc_imp_inh                            [conj_cone]
% 11.62/2.00  --conj_cone_tolerance                   3.
% 11.62/2.00  --extra_neg_conj                        none
% 11.62/2.00  --large_theory_mode                     true
% 11.62/2.00  --prolific_symb_bound                   200
% 11.62/2.00  --lt_threshold                          2000
% 11.62/2.00  --clause_weak_htbl                      true
% 11.62/2.00  --gc_record_bc_elim                     false
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing Options
% 11.62/2.00  
% 11.62/2.00  --preprocessing_flag                    true
% 11.62/2.00  --time_out_prep_mult                    0.1
% 11.62/2.00  --splitting_mode                        input
% 11.62/2.00  --splitting_grd                         true
% 11.62/2.00  --splitting_cvd                         false
% 11.62/2.00  --splitting_cvd_svl                     false
% 11.62/2.00  --splitting_nvd                         32
% 11.62/2.00  --sub_typing                            true
% 11.62/2.00  --prep_gs_sim                           true
% 11.62/2.00  --prep_unflatten                        true
% 11.62/2.00  --prep_res_sim                          true
% 11.62/2.00  --prep_upred                            true
% 11.62/2.00  --prep_sem_filter                       exhaustive
% 11.62/2.00  --prep_sem_filter_out                   false
% 11.62/2.00  --pred_elim                             true
% 11.62/2.00  --res_sim_input                         true
% 11.62/2.00  --eq_ax_congr_red                       true
% 11.62/2.00  --pure_diseq_elim                       true
% 11.62/2.00  --brand_transform                       false
% 11.62/2.00  --non_eq_to_eq                          false
% 11.62/2.00  --prep_def_merge                        true
% 11.62/2.00  --prep_def_merge_prop_impl              false
% 11.62/2.00  --prep_def_merge_mbd                    true
% 11.62/2.00  --prep_def_merge_tr_red                 false
% 11.62/2.00  --prep_def_merge_tr_cl                  false
% 11.62/2.00  --smt_preprocessing                     true
% 11.62/2.00  --smt_ac_axioms                         fast
% 11.62/2.00  --preprocessed_out                      false
% 11.62/2.00  --preprocessed_stats                    false
% 11.62/2.00  
% 11.62/2.00  ------ Abstraction refinement Options
% 11.62/2.00  
% 11.62/2.00  --abstr_ref                             []
% 11.62/2.00  --abstr_ref_prep                        false
% 11.62/2.00  --abstr_ref_until_sat                   false
% 11.62/2.00  --abstr_ref_sig_restrict                funpre
% 11.62/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.62/2.00  --abstr_ref_under                       []
% 11.62/2.00  
% 11.62/2.00  ------ SAT Options
% 11.62/2.00  
% 11.62/2.00  --sat_mode                              false
% 11.62/2.00  --sat_fm_restart_options                ""
% 11.62/2.00  --sat_gr_def                            false
% 11.62/2.00  --sat_epr_types                         true
% 11.62/2.00  --sat_non_cyclic_types                  false
% 11.62/2.00  --sat_finite_models                     false
% 11.62/2.00  --sat_fm_lemmas                         false
% 11.62/2.00  --sat_fm_prep                           false
% 11.62/2.00  --sat_fm_uc_incr                        true
% 11.62/2.00  --sat_out_model                         small
% 11.62/2.00  --sat_out_clauses                       false
% 11.62/2.00  
% 11.62/2.00  ------ QBF Options
% 11.62/2.00  
% 11.62/2.00  --qbf_mode                              false
% 11.62/2.00  --qbf_elim_univ                         false
% 11.62/2.00  --qbf_dom_inst                          none
% 11.62/2.00  --qbf_dom_pre_inst                      false
% 11.62/2.00  --qbf_sk_in                             false
% 11.62/2.00  --qbf_pred_elim                         true
% 11.62/2.00  --qbf_split                             512
% 11.62/2.00  
% 11.62/2.00  ------ BMC1 Options
% 11.62/2.00  
% 11.62/2.00  --bmc1_incremental                      false
% 11.62/2.00  --bmc1_axioms                           reachable_all
% 11.62/2.00  --bmc1_min_bound                        0
% 11.62/2.00  --bmc1_max_bound                        -1
% 11.62/2.00  --bmc1_max_bound_default                -1
% 11.62/2.00  --bmc1_symbol_reachability              true
% 11.62/2.00  --bmc1_property_lemmas                  false
% 11.62/2.00  --bmc1_k_induction                      false
% 11.62/2.00  --bmc1_non_equiv_states                 false
% 11.62/2.00  --bmc1_deadlock                         false
% 11.62/2.00  --bmc1_ucm                              false
% 11.62/2.00  --bmc1_add_unsat_core                   none
% 11.62/2.00  --bmc1_unsat_core_children              false
% 11.62/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.62/2.00  --bmc1_out_stat                         full
% 11.62/2.00  --bmc1_ground_init                      false
% 11.62/2.00  --bmc1_pre_inst_next_state              false
% 11.62/2.00  --bmc1_pre_inst_state                   false
% 11.62/2.00  --bmc1_pre_inst_reach_state             false
% 11.62/2.00  --bmc1_out_unsat_core                   false
% 11.62/2.00  --bmc1_aig_witness_out                  false
% 11.62/2.00  --bmc1_verbose                          false
% 11.62/2.00  --bmc1_dump_clauses_tptp                false
% 11.62/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.62/2.00  --bmc1_dump_file                        -
% 11.62/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.62/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.62/2.00  --bmc1_ucm_extend_mode                  1
% 11.62/2.00  --bmc1_ucm_init_mode                    2
% 11.62/2.00  --bmc1_ucm_cone_mode                    none
% 11.62/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.62/2.00  --bmc1_ucm_relax_model                  4
% 11.62/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.62/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.62/2.00  --bmc1_ucm_layered_model                none
% 11.62/2.00  --bmc1_ucm_max_lemma_size               10
% 11.62/2.00  
% 11.62/2.00  ------ AIG Options
% 11.62/2.00  
% 11.62/2.00  --aig_mode                              false
% 11.62/2.00  
% 11.62/2.00  ------ Instantiation Options
% 11.62/2.00  
% 11.62/2.00  --instantiation_flag                    true
% 11.62/2.00  --inst_sos_flag                         true
% 11.62/2.00  --inst_sos_phase                        true
% 11.62/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.62/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.62/2.00  --inst_lit_sel_side                     none
% 11.62/2.00  --inst_solver_per_active                1400
% 11.62/2.00  --inst_solver_calls_frac                1.
% 11.62/2.00  --inst_passive_queue_type               priority_queues
% 11.62/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.62/2.00  --inst_passive_queues_freq              [25;2]
% 11.62/2.00  --inst_dismatching                      true
% 11.62/2.00  --inst_eager_unprocessed_to_passive     true
% 11.62/2.00  --inst_prop_sim_given                   true
% 11.62/2.00  --inst_prop_sim_new                     false
% 11.62/2.00  --inst_subs_new                         false
% 11.62/2.00  --inst_eq_res_simp                      false
% 11.62/2.00  --inst_subs_given                       false
% 11.62/2.00  --inst_orphan_elimination               true
% 11.62/2.00  --inst_learning_loop_flag               true
% 11.62/2.00  --inst_learning_start                   3000
% 11.62/2.00  --inst_learning_factor                  2
% 11.62/2.00  --inst_start_prop_sim_after_learn       3
% 11.62/2.00  --inst_sel_renew                        solver
% 11.62/2.00  --inst_lit_activity_flag                true
% 11.62/2.00  --inst_restr_to_given                   false
% 11.62/2.00  --inst_activity_threshold               500
% 11.62/2.00  --inst_out_proof                        true
% 11.62/2.00  
% 11.62/2.00  ------ Resolution Options
% 11.62/2.00  
% 11.62/2.00  --resolution_flag                       false
% 11.62/2.00  --res_lit_sel                           adaptive
% 11.62/2.00  --res_lit_sel_side                      none
% 11.62/2.00  --res_ordering                          kbo
% 11.62/2.00  --res_to_prop_solver                    active
% 11.62/2.00  --res_prop_simpl_new                    false
% 11.62/2.00  --res_prop_simpl_given                  true
% 11.62/2.00  --res_passive_queue_type                priority_queues
% 11.62/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.62/2.00  --res_passive_queues_freq               [15;5]
% 11.62/2.00  --res_forward_subs                      full
% 11.62/2.00  --res_backward_subs                     full
% 11.62/2.00  --res_forward_subs_resolution           true
% 11.62/2.00  --res_backward_subs_resolution          true
% 11.62/2.00  --res_orphan_elimination                true
% 11.62/2.00  --res_time_limit                        2.
% 11.62/2.00  --res_out_proof                         true
% 11.62/2.00  
% 11.62/2.00  ------ Superposition Options
% 11.62/2.00  
% 11.62/2.00  --superposition_flag                    true
% 11.62/2.00  --sup_passive_queue_type                priority_queues
% 11.62/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.62/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.62/2.00  --demod_completeness_check              fast
% 11.62/2.00  --demod_use_ground                      true
% 11.62/2.00  --sup_to_prop_solver                    passive
% 11.62/2.00  --sup_prop_simpl_new                    true
% 11.62/2.00  --sup_prop_simpl_given                  true
% 11.62/2.00  --sup_fun_splitting                     true
% 11.62/2.00  --sup_smt_interval                      50000
% 11.62/2.00  
% 11.62/2.00  ------ Superposition Simplification Setup
% 11.62/2.00  
% 11.62/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.62/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.62/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.62/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.62/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.62/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.62/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.62/2.00  --sup_immed_triv                        [TrivRules]
% 11.62/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/2.00  --sup_immed_bw_main                     []
% 11.62/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.62/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.62/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.62/2.00  --sup_input_bw                          []
% 11.62/2.00  
% 11.62/2.00  ------ Combination Options
% 11.62/2.00  
% 11.62/2.00  --comb_res_mult                         3
% 11.62/2.00  --comb_sup_mult                         2
% 11.62/2.00  --comb_inst_mult                        10
% 11.62/2.00  
% 11.62/2.00  ------ Debug Options
% 11.62/2.00  
% 11.62/2.00  --dbg_backtrace                         false
% 11.62/2.00  --dbg_dump_prop_clauses                 false
% 11.62/2.00  --dbg_dump_prop_clauses_file            -
% 11.62/2.00  --dbg_out_stat                          false
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  ------ Proving...
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  % SZS status Theorem for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  fof(f19,conjecture,(
% 11.62/2.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f20,negated_conjecture,(
% 11.62/2.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.62/2.00    inference(negated_conjecture,[],[f19])).
% 11.62/2.00  
% 11.62/2.00  fof(f40,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f20])).
% 11.62/2.00  
% 11.62/2.00  fof(f41,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.62/2.00    inference(flattening,[],[f40])).
% 11.62/2.00  
% 11.62/2.00  fof(f58,plain,(
% 11.62/2.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f57,plain,(
% 11.62/2.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f56,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f55,plain,(
% 11.62/2.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f54,plain,(
% 11.62/2.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f53,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f59,plain,(
% 11.62/2.00    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 11.62/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f41,f58,f57,f56,f55,f54,f53])).
% 11.62/2.00  
% 11.62/2.00  fof(f96,plain,(
% 11.62/2.00    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f7,axiom,(
% 11.62/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f47,plain,(
% 11.62/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.62/2.00    inference(nnf_transformation,[],[f7])).
% 11.62/2.00  
% 11.62/2.00  fof(f71,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f47])).
% 11.62/2.00  
% 11.62/2.00  fof(f6,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f23,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f6])).
% 11.62/2.00  
% 11.62/2.00  fof(f70,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f23])).
% 11.62/2.00  
% 11.62/2.00  fof(f72,plain,(
% 11.62/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f47])).
% 11.62/2.00  
% 11.62/2.00  fof(f100,plain,(
% 11.62/2.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f16,axiom,(
% 11.62/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f34,plain,(
% 11.62/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.62/2.00    inference(ennf_transformation,[],[f16])).
% 11.62/2.00  
% 11.62/2.00  fof(f35,plain,(
% 11.62/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.62/2.00    inference(flattening,[],[f34])).
% 11.62/2.00  
% 11.62/2.00  fof(f84,plain,(
% 11.62/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f35])).
% 11.62/2.00  
% 11.62/2.00  fof(f98,plain,(
% 11.62/2.00    v1_funct_1(sK4)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f103,plain,(
% 11.62/2.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f101,plain,(
% 11.62/2.00    v1_funct_1(sK5)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f17,axiom,(
% 11.62/2.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f36,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f17])).
% 11.62/2.00  
% 11.62/2.00  fof(f37,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/2.00    inference(flattening,[],[f36])).
% 11.62/2.00  
% 11.62/2.00  fof(f51,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/2.00    inference(nnf_transformation,[],[f37])).
% 11.62/2.00  
% 11.62/2.00  fof(f52,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.62/2.00    inference(flattening,[],[f51])).
% 11.62/2.00  
% 11.62/2.00  fof(f86,plain,(
% 11.62/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f52])).
% 11.62/2.00  
% 11.62/2.00  fof(f111,plain,(
% 11.62/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(equality_resolution,[],[f86])).
% 11.62/2.00  
% 11.62/2.00  fof(f18,axiom,(
% 11.62/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f38,plain,(
% 11.62/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f18])).
% 11.62/2.00  
% 11.62/2.00  fof(f39,plain,(
% 11.62/2.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.62/2.00    inference(flattening,[],[f38])).
% 11.62/2.00  
% 11.62/2.00  fof(f88,plain,(
% 11.62/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f89,plain,(
% 11.62/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f90,plain,(
% 11.62/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f92,plain,(
% 11.62/2.00    ~v1_xboole_0(sK1)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f95,plain,(
% 11.62/2.00    ~v1_xboole_0(sK3)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f102,plain,(
% 11.62/2.00    v1_funct_2(sK5,sK3,sK1)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f93,plain,(
% 11.62/2.00    ~v1_xboole_0(sK2)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f99,plain,(
% 11.62/2.00    v1_funct_2(sK4,sK2,sK1)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f13,axiom,(
% 11.62/2.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f30,plain,(
% 11.62/2.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f13])).
% 11.62/2.00  
% 11.62/2.00  fof(f31,plain,(
% 11.62/2.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.62/2.00    inference(flattening,[],[f30])).
% 11.62/2.00  
% 11.62/2.00  fof(f50,plain,(
% 11.62/2.00    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.62/2.00    inference(nnf_transformation,[],[f31])).
% 11.62/2.00  
% 11.62/2.00  fof(f80,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f50])).
% 11.62/2.00  
% 11.62/2.00  fof(f97,plain,(
% 11.62/2.00    r1_subset_1(sK2,sK3)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f1,axiom,(
% 11.62/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f42,plain,(
% 11.62/2.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.62/2.00    inference(nnf_transformation,[],[f1])).
% 11.62/2.00  
% 11.62/2.00  fof(f60,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f14,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f32,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/2.00    inference(ennf_transformation,[],[f14])).
% 11.62/2.00  
% 11.62/2.00  fof(f82,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f32])).
% 11.62/2.00  
% 11.62/2.00  fof(f3,axiom,(
% 11.62/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f43,plain,(
% 11.62/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.62/2.00    inference(nnf_transformation,[],[f3])).
% 11.62/2.00  
% 11.62/2.00  fof(f44,plain,(
% 11.62/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.62/2.00    inference(flattening,[],[f43])).
% 11.62/2.00  
% 11.62/2.00  fof(f64,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.62/2.00    inference(cnf_transformation,[],[f44])).
% 11.62/2.00  
% 11.62/2.00  fof(f105,plain,(
% 11.62/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.62/2.00    inference(equality_resolution,[],[f64])).
% 11.62/2.00  
% 11.62/2.00  fof(f5,axiom,(
% 11.62/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f45,plain,(
% 11.62/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.62/2.00    inference(nnf_transformation,[],[f5])).
% 11.62/2.00  
% 11.62/2.00  fof(f46,plain,(
% 11.62/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.62/2.00    inference(flattening,[],[f45])).
% 11.62/2.00  
% 11.62/2.00  fof(f69,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.62/2.00    inference(cnf_transformation,[],[f46])).
% 11.62/2.00  
% 11.62/2.00  fof(f107,plain,(
% 11.62/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.62/2.00    inference(equality_resolution,[],[f69])).
% 11.62/2.00  
% 11.62/2.00  fof(f15,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f21,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.62/2.00    inference(pure_predicate_removal,[],[f15])).
% 11.62/2.00  
% 11.62/2.00  fof(f33,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.62/2.00    inference(ennf_transformation,[],[f21])).
% 11.62/2.00  
% 11.62/2.00  fof(f83,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f33])).
% 11.62/2.00  
% 11.62/2.00  fof(f11,axiom,(
% 11.62/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f27,plain,(
% 11.62/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.62/2.00    inference(ennf_transformation,[],[f11])).
% 11.62/2.00  
% 11.62/2.00  fof(f28,plain,(
% 11.62/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(flattening,[],[f27])).
% 11.62/2.00  
% 11.62/2.00  fof(f77,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f28])).
% 11.62/2.00  
% 11.62/2.00  fof(f12,axiom,(
% 11.62/2.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f29,plain,(
% 11.62/2.00    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(ennf_transformation,[],[f12])).
% 11.62/2.00  
% 11.62/2.00  fof(f49,plain,(
% 11.62/2.00    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(nnf_transformation,[],[f29])).
% 11.62/2.00  
% 11.62/2.00  fof(f78,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f49])).
% 11.62/2.00  
% 11.62/2.00  fof(f9,axiom,(
% 11.62/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f75,plain,(
% 11.62/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f9])).
% 11.62/2.00  
% 11.62/2.00  fof(f2,axiom,(
% 11.62/2.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f22,plain,(
% 11.62/2.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.62/2.00    inference(ennf_transformation,[],[f2])).
% 11.62/2.00  
% 11.62/2.00  fof(f62,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f22])).
% 11.62/2.00  
% 11.62/2.00  fof(f79,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f49])).
% 11.62/2.00  
% 11.62/2.00  fof(f4,axiom,(
% 11.62/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f66,plain,(
% 11.62/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f4])).
% 11.62/2.00  
% 11.62/2.00  fof(f8,axiom,(
% 11.62/2.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 11.62/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f24,plain,(
% 11.62/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(ennf_transformation,[],[f8])).
% 11.62/2.00  
% 11.62/2.00  fof(f48,plain,(
% 11.62/2.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.62/2.00    inference(nnf_transformation,[],[f24])).
% 11.62/2.00  
% 11.62/2.00  fof(f73,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f48])).
% 11.62/2.00  
% 11.62/2.00  fof(f65,plain,(
% 11.62/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f44])).
% 11.62/2.00  
% 11.62/2.00  fof(f85,plain,(
% 11.62/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f52])).
% 11.62/2.00  
% 11.62/2.00  fof(f112,plain,(
% 11.62/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.62/2.00    inference(equality_resolution,[],[f85])).
% 11.62/2.00  
% 11.62/2.00  fof(f104,plain,(
% 11.62/2.00    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f94,plain,(
% 11.62/2.00    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  fof(f91,plain,(
% 11.62/2.00    ~v1_xboole_0(sK0)),
% 11.62/2.00    inference(cnf_transformation,[],[f59])).
% 11.62/2.00  
% 11.62/2.00  cnf(c_39,negated_conjecture,
% 11.62/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2081,plain,
% 11.62/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2098,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.62/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4201,plain,
% 11.62/2.00      ( r1_tarski(sK3,sK0) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2081,c_2098]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_10,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/2.00      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_11,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_323,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.62/2.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_324,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_323]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_411,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.62/2.00      inference(bin_hyper_res,[status(thm)],[c_10,c_324]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2073,plain,
% 11.62/2.00      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 11.62/2.00      | r1_tarski(X2,X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_17792,plain,
% 11.62/2.00      ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4201,c_2073]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_35,negated_conjecture,
% 11.62/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.62/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2084,plain,
% 11.62/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_24,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.62/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2092,plain,
% 11.62/2.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 11.62/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5122,plain,
% 11.62/2.00      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2084,c_2092]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_37,negated_conjecture,
% 11.62/2.00      ( v1_funct_1(sK4) ),
% 11.62/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_52,plain,
% 11.62/2.00      ( v1_funct_1(sK4) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5407,plain,
% 11.62/2.00      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5122,c_52]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_32,negated_conjecture,
% 11.62/2.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.62/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2087,plain,
% 11.62/2.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5121,plain,
% 11.62/2.00      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 11.62/2.00      | v1_funct_1(sK5) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2087,c_2092]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34,negated_conjecture,
% 11.62/2.00      ( v1_funct_1(sK5) ),
% 11.62/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_55,plain,
% 11.62/2.00      ( v1_funct_1(sK5) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5241,plain,
% 11.62/2.00      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5121,c_55]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_26,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_30,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_29,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f89]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_28,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_242,plain,
% 11.62/2.00      ( ~ v1_funct_1(X3)
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_26,c_30,c_29,c_28]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_243,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_242]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2074,plain,
% 11.62/2.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 11.62/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.62/2.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 11.62/2.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 11.62/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/2.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 11.62/2.00      | v1_funct_1(X2) != iProver_top
% 11.62/2.00      | v1_funct_1(X5) != iProver_top
% 11.62/2.00      | v1_xboole_0(X3) = iProver_top
% 11.62/2.00      | v1_xboole_0(X1) = iProver_top
% 11.62/2.00      | v1_xboole_0(X4) = iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5246,plain,
% 11.62/2.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 11.62/2.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 11.62/2.00      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | v1_funct_1(X1) != iProver_top
% 11.62/2.00      | v1_funct_1(sK5) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | v1_xboole_0(X2) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK1) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK3) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_5241,c_2074]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_43,negated_conjecture,
% 11.62/2.00      ( ~ v1_xboole_0(sK1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_46,plain,
% 11.62/2.00      ( v1_xboole_0(sK1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_40,negated_conjecture,
% 11.62/2.00      ( ~ v1_xboole_0(sK3) ),
% 11.62/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_49,plain,
% 11.62/2.00      ( v1_xboole_0(sK3) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_33,negated_conjecture,
% 11.62/2.00      ( v1_funct_2(sK5,sK3,sK1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f102]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_56,plain,
% 11.62/2.00      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_57,plain,
% 11.62/2.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6679,plain,
% 11.62/2.00      ( v1_funct_1(X1) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 11.62/2.00      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | v1_xboole_0(X2) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5246,c_46,c_49,c_55,c_56,c_57]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6680,plain,
% 11.62/2.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 11.62/2.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | v1_funct_1(X1) != iProver_top
% 11.62/2.00      | v1_xboole_0(X2) = iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_6679]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6686,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 11.62/2.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_5407,c_6680]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_42,negated_conjecture,
% 11.62/2.00      ( ~ v1_xboole_0(sK2) ),
% 11.62/2.00      inference(cnf_transformation,[],[f93]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_47,plain,
% 11.62/2.00      ( v1_xboole_0(sK2) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_36,negated_conjecture,
% 11.62/2.00      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_53,plain,
% 11.62/2.00      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_54,plain,
% 11.62/2.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6691,plain,
% 11.62/2.00      ( v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_6686,c_47,c_52,c_53,c_54]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6692,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_6691]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20799,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_17792,c_6692]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_21,plain,
% 11.62/2.00      ( ~ r1_subset_1(X0,X1)
% 11.62/2.00      | r1_xboole_0(X0,X1)
% 11.62/2.00      | v1_xboole_0(X0)
% 11.62/2.00      | v1_xboole_0(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_38,negated_conjecture,
% 11.62/2.00      ( r1_subset_1(sK2,sK3) ),
% 11.62/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_555,plain,
% 11.62/2.00      ( r1_xboole_0(X0,X1)
% 11.62/2.00      | v1_xboole_0(X0)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | sK3 != X1
% 11.62/2.00      | sK2 != X0 ),
% 11.62/2.00      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_556,plain,
% 11.62/2.00      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 11.62/2.00      inference(unflattening,[status(thm)],[c_555]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_558,plain,
% 11.62/2.00      ( r1_xboole_0(sK2,sK3) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_556,c_42,c_40]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2072,plain,
% 11.62/2.00      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1,plain,
% 11.62/2.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2104,plain,
% 11.62/2.00      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 11.62/2.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3998,plain,
% 11.62/2.00      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2072,c_2104]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_22,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | v1_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2093,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4259,plain,
% 11.62/2.00      ( v1_relat_1(sK5) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2087,c_2093]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4,plain,
% 11.62/2.00      ( r1_tarski(X0,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2101,plain,
% 11.62/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2099,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.62/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7,plain,
% 11.62/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_23,plain,
% 11.62/2.00      ( v4_relat_1(X0,X1)
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.62/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_17,plain,
% 11.62/2.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_568,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ v1_relat_1(X0)
% 11.62/2.00      | k7_relat_1(X0,X1) = X0 ),
% 11.62/2.00      inference(resolution,[status(thm)],[c_23,c_17]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_572,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | k7_relat_1(X0,X1) = X0 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_568,c_23,c_22,c_17]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2071,plain,
% 11.62/2.00      ( k7_relat_1(X0,X1) = X0
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_572]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3296,plain,
% 11.62/2.00      ( k7_relat_1(X0,X1) = X0
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_7,c_2071]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4253,plain,
% 11.62/2.00      ( k7_relat_1(X0,X1) = X0
% 11.62/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2099,c_3296]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4472,plain,
% 11.62/2.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2101,c_4253]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_19,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(X0),X1)
% 11.62/2.00      | ~ v1_relat_1(X0)
% 11.62/2.00      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2094,plain,
% 11.62/2.00      ( k7_relat_1(X0,X1) != k1_xboole_0
% 11.62/2.00      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5050,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 11.62/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4472,c_2094]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15,plain,
% 11.62/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2097,plain,
% 11.62/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3375,plain,
% 11.62/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_7,c_2097]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6882,plain,
% 11.62/2.00      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5050,c_3375]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2,plain,
% 11.62/2.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2103,plain,
% 11.62/2.00      ( r1_xboole_0(X0,X1) != iProver_top
% 11.62/2.00      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6889,plain,
% 11.62/2.00      ( r1_xboole_0(X0,k1_relat_1(k1_xboole_0)) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_6882,c_2103]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_18,plain,
% 11.62/2.00      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.62/2.00      | ~ v1_relat_1(X0)
% 11.62/2.00      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2095,plain,
% 11.62/2.00      ( k7_relat_1(X0,X1) = k1_xboole_0
% 11.62/2.00      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7341,plain,
% 11.62/2.00      ( k7_relat_1(X0,k1_relat_1(k1_xboole_0)) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_6889,c_2095]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6,plain,
% 11.62/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2100,plain,
% 11.62/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_14,plain,
% 11.62/2.00      ( ~ v4_relat_1(X0,X1)
% 11.62/2.00      | r1_tarski(k1_relat_1(X0),X1)
% 11.62/2.00      | ~ v1_relat_1(X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_585,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | r1_tarski(k1_relat_1(X0),X1)
% 11.62/2.00      | ~ v1_relat_1(X0) ),
% 11.62/2.00      inference(resolution,[status(thm)],[c_23,c_14]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_589,plain,
% 11.62/2.00      ( r1_tarski(k1_relat_1(X0),X1)
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_585,c_22]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_590,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_589]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2070,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.62/2.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4210,plain,
% 11.62/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.62/2.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2099,c_2070]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8297,plain,
% 11.62/2.00      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2100,c_4210]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.62/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2102,plain,
% 11.62/2.00      ( X0 = X1
% 11.62/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.62/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4696,plain,
% 11.62/2.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2100,c_2102]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8510,plain,
% 11.62/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_8297,c_4696]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_10233,plain,
% 11.62/2.00      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 11.62/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_7341,c_8510]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_10237,plain,
% 11.62/2.00      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4259,c_10233]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20805,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_20799,c_3998,c_10237]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20806,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_20805,c_17792]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4260,plain,
% 11.62/2.00      ( v1_relat_1(sK4) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2084,c_2093]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_10238,plain,
% 11.62/2.00      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4260,c_10233]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20807,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | k1_xboole_0 != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_20806,c_3998,c_10238]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20808,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(equality_resolution_simp,[status(thm)],[c_20807]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_27,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.62/2.00      inference(cnf_transformation,[],[f112]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_235,plain,
% 11.62/2.00      ( ~ v1_funct_1(X3)
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_27,c_30,c_29,c_28]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_236,plain,
% 11.62/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.62/2.00      | ~ v1_funct_2(X3,X4,X2)
% 11.62/2.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.62/2.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.62/2.00      | ~ v1_funct_1(X0)
% 11.62/2.00      | ~ v1_funct_1(X3)
% 11.62/2.00      | v1_xboole_0(X1)
% 11.62/2.00      | v1_xboole_0(X2)
% 11.62/2.00      | v1_xboole_0(X4)
% 11.62/2.00      | v1_xboole_0(X5)
% 11.62/2.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_235]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2075,plain,
% 11.62/2.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 11.62/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.62/2.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 11.62/2.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 11.62/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.62/2.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 11.62/2.00      | v1_funct_1(X2) != iProver_top
% 11.62/2.00      | v1_funct_1(X5) != iProver_top
% 11.62/2.00      | v1_xboole_0(X3) = iProver_top
% 11.62/2.00      | v1_xboole_0(X1) = iProver_top
% 11.62/2.00      | v1_xboole_0(X4) = iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_236]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5245,plain,
% 11.62/2.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 11.62/2.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 11.62/2.00      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | v1_funct_1(X1) != iProver_top
% 11.62/2.00      | v1_funct_1(sK5) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | v1_xboole_0(X2) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK1) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK3) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_5241,c_2075]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6451,plain,
% 11.62/2.00      ( v1_funct_1(X1) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 11.62/2.00      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | v1_xboole_0(X2) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_5245,c_46,c_49,c_55,c_56,c_57]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6452,plain,
% 11.62/2.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 11.62/2.00      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 11.62/2.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 11.62/2.00      | v1_funct_1(X1) != iProver_top
% 11.62/2.00      | v1_xboole_0(X2) = iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_6451]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6458,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 11.62/2.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 11.62/2.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | v1_funct_1(sK4) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_5407,c_6452]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6576,plain,
% 11.62/2.00      ( v1_xboole_0(X0) = iProver_top
% 11.62/2.00      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_6458,c_47,c_52,c_53,c_54]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6577,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_6576]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20800,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_17792,c_6577]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20801,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_20800,c_3998,c_10237]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20802,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_20801,c_17792]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20803,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | k1_xboole_0 != k1_xboole_0
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_20802,c_3998,c_10238]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20804,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.62/2.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 11.62/2.00      | v1_xboole_0(sK0) = iProver_top ),
% 11.62/2.00      inference(equality_resolution_simp,[status(thm)],[c_20803]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_31,negated_conjecture,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5244,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_5241,c_31]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5410,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_5407,c_5244]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20784,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_17792,c_5410]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20785,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.62/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_20784,c_3998,c_10237,c_10238]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20786,plain,
% 11.62/2.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.62/2.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 11.62/2.00      inference(equality_resolution_simp,[status(thm)],[c_20785]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_50,plain,
% 11.62/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_41,negated_conjecture,
% 11.62/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 11.62/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_48,plain,
% 11.62/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_44,negated_conjecture,
% 11.62/2.00      ( ~ v1_xboole_0(sK0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_45,plain,
% 11.62/2.00      ( v1_xboole_0(sK0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(contradiction,plain,
% 11.62/2.00      ( $false ),
% 11.62/2.00      inference(minisat,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_20808,c_20804,c_20786,c_50,c_48,c_45]) ).
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
% 11.62/2.00  parsing_time:                           0.015
% 11.62/2.00  unif_index_cands_time:                  0.
% 11.62/2.00  unif_index_add_time:                    0.
% 11.62/2.00  orderings_time:                         0.
% 11.62/2.00  out_proof_time:                         0.019
% 11.62/2.00  total_time:                             1.187
% 11.62/2.00  num_of_symbols:                         56
% 11.62/2.00  num_of_terms:                           48441
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing
% 11.62/2.00  
% 11.62/2.00  num_of_splits:                          0
% 11.62/2.00  num_of_split_atoms:                     0
% 11.62/2.00  num_of_reused_defs:                     0
% 11.62/2.00  num_eq_ax_congr_red:                    18
% 11.62/2.00  num_of_sem_filtered_clauses:            1
% 11.62/2.00  num_of_subtypes:                        0
% 11.62/2.00  monotx_restored_types:                  0
% 11.62/2.00  sat_num_of_epr_types:                   0
% 11.62/2.00  sat_num_of_non_cyclic_types:            0
% 11.62/2.00  sat_guarded_non_collapsed_types:        0
% 11.62/2.00  num_pure_diseq_elim:                    0
% 11.62/2.00  simp_replaced_by:                       0
% 11.62/2.00  res_preprocessed:                       200
% 11.62/2.00  prep_upred:                             0
% 11.62/2.00  prep_unflattend:                        12
% 11.62/2.00  smt_new_axioms:                         0
% 11.62/2.00  pred_elim_cands:                        7
% 11.62/2.00  pred_elim:                              2
% 11.62/2.00  pred_elim_cl:                           3
% 11.62/2.00  pred_elim_cycles:                       4
% 11.62/2.00  merged_defs:                            16
% 11.62/2.00  merged_defs_ncl:                        0
% 11.62/2.00  bin_hyper_res:                          17
% 11.62/2.00  prep_cycles:                            4
% 11.62/2.00  pred_elim_time:                         0.006
% 11.62/2.00  splitting_time:                         0.
% 11.62/2.00  sem_filter_time:                        0.
% 11.62/2.00  monotx_time:                            0.001
% 11.62/2.00  subtype_inf_time:                       0.
% 11.62/2.00  
% 11.62/2.00  ------ Problem properties
% 11.62/2.00  
% 11.62/2.00  clauses:                                41
% 11.62/2.00  conjectures:                            13
% 11.62/2.00  epr:                                    13
% 11.62/2.00  horn:                                   34
% 11.62/2.00  ground:                                 14
% 11.62/2.00  unary:                                  18
% 11.62/2.00  binary:                                 9
% 11.62/2.00  lits:                                   144
% 11.62/2.00  lits_eq:                                24
% 11.62/2.00  fd_pure:                                0
% 11.62/2.00  fd_pseudo:                              0
% 11.62/2.00  fd_cond:                                1
% 11.62/2.00  fd_pseudo_cond:                         1
% 11.62/2.00  ac_symbols:                             0
% 11.62/2.00  
% 11.62/2.00  ------ Propositional Solver
% 11.62/2.00  
% 11.62/2.00  prop_solver_calls:                      30
% 11.62/2.00  prop_fast_solver_calls:                 3492
% 11.62/2.00  smt_solver_calls:                       0
% 11.62/2.00  smt_fast_solver_calls:                  0
% 11.62/2.00  prop_num_of_clauses:                    11824
% 11.62/2.00  prop_preprocess_simplified:             18323
% 11.62/2.00  prop_fo_subsumed:                       204
% 11.62/2.00  prop_solver_time:                       0.
% 11.62/2.00  smt_solver_time:                        0.
% 11.62/2.00  smt_fast_solver_time:                   0.
% 11.62/2.00  prop_fast_solver_time:                  0.
% 11.62/2.00  prop_unsat_core_time:                   0.001
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
% 11.62/2.00  inst_num_of_clauses:                    2691
% 11.62/2.00  inst_num_in_passive:                    149
% 11.62/2.00  inst_num_in_active:                     1211
% 11.62/2.00  inst_num_in_unprocessed:                1331
% 11.62/2.00  inst_num_of_loops:                      1550
% 11.62/2.00  inst_num_of_learning_restarts:          0
% 11.62/2.00  inst_num_moves_active_passive:          336
% 11.62/2.00  inst_lit_activity:                      0
% 11.62/2.00  inst_lit_activity_moves:                1
% 11.62/2.00  inst_num_tautologies:                   0
% 11.62/2.00  inst_num_prop_implied:                  0
% 11.62/2.00  inst_num_existing_simplified:           0
% 11.62/2.00  inst_num_eq_res_simplified:             0
% 11.62/2.00  inst_num_child_elim:                    0
% 11.62/2.00  inst_num_of_dismatching_blockings:      672
% 11.62/2.00  inst_num_of_non_proper_insts:           2948
% 11.62/2.00  inst_num_of_duplicates:                 0
% 11.62/2.00  inst_inst_num_from_inst_to_res:         0
% 11.62/2.00  inst_dismatching_checking_time:         0.
% 11.62/2.00  
% 11.62/2.00  ------ Resolution
% 11.62/2.00  
% 11.62/2.00  res_num_of_clauses:                     0
% 11.62/2.00  res_num_in_passive:                     0
% 11.62/2.00  res_num_in_active:                      0
% 11.62/2.00  res_num_of_loops:                       204
% 11.62/2.00  res_forward_subset_subsumed:            108
% 11.62/2.00  res_backward_subset_subsumed:           0
% 11.62/2.00  res_forward_subsumed:                   0
% 11.62/2.00  res_backward_subsumed:                  0
% 11.62/2.00  res_forward_subsumption_resolution:     0
% 11.62/2.00  res_backward_subsumption_resolution:    0
% 11.62/2.00  res_clause_to_clause_subsumption:       2154
% 11.62/2.00  res_orphan_elimination:                 0
% 11.62/2.00  res_tautology_del:                      54
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
% 11.62/2.00  sup_num_of_clauses:                     524
% 11.62/2.00  sup_num_in_active:                      274
% 11.62/2.00  sup_num_in_passive:                     250
% 11.62/2.00  sup_num_of_loops:                       309
% 11.62/2.00  sup_fw_superposition:                   450
% 11.62/2.00  sup_bw_superposition:                   331
% 11.62/2.00  sup_immediate_simplified:               201
% 11.62/2.00  sup_given_eliminated:                   5
% 11.62/2.00  comparisons_done:                       0
% 11.62/2.00  comparisons_avoided:                    0
% 11.62/2.00  
% 11.62/2.00  ------ Simplifications
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  sim_fw_subset_subsumed:                 21
% 11.62/2.00  sim_bw_subset_subsumed:                 3
% 11.62/2.00  sim_fw_subsumed:                        34
% 11.62/2.00  sim_bw_subsumed:                        30
% 11.62/2.00  sim_fw_subsumption_res:                 0
% 11.62/2.00  sim_bw_subsumption_res:                 0
% 11.62/2.00  sim_tautology_del:                      1
% 11.62/2.00  sim_eq_tautology_del:                   17
% 11.62/2.00  sim_eq_res_simp:                        7
% 11.62/2.00  sim_fw_demodulated:                     77
% 11.62/2.00  sim_bw_demodulated:                     14
% 11.62/2.00  sim_light_normalised:                   108
% 11.62/2.00  sim_joinable_taut:                      0
% 11.62/2.00  sim_joinable_simp:                      0
% 11.62/2.00  sim_ac_normalised:                      0
% 11.62/2.00  sim_smt_subsumption:                    0
% 11.62/2.00  
%------------------------------------------------------------------------------
