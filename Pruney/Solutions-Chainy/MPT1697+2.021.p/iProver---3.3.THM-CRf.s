%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:26 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.38s
% Verified   : 
% Statistics : Number of formulae       :  278 (6090 expanded)
%              Number of clauses        :  179 (1647 expanded)
%              Number of leaves         :   25 (2000 expanded)
%              Depth                    :   34
%              Number of atoms          : 1295 (59485 expanded)
%              Number of equality atoms :  496 (13488 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f55,plain,(
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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f56,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f43,f55,f54,f53,f52,f51,f50])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f106,plain,(
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
    inference(equality_resolution,[],[f79])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f86,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f92,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f88,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f63,f62])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f49])).

fof(f107,plain,(
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
    inference(equality_resolution,[],[f78])).

fof(f97,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f56])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1256,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_2103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1256])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1277,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | k9_subset_1(X1_56,X2_56,X0_56) = k1_setfam_1(k2_tarski(X2_56,X0_56)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2084,plain,
    ( k9_subset_1(X0_56,X1_56,X2_56) = k1_setfam_1(k2_tarski(X1_56,X2_56))
    | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1277])).

cnf(c_2752,plain,
    ( k9_subset_1(sK0,X0_56,sK3) = k1_setfam_1(k2_tarski(X0_56,sK3)) ),
    inference(superposition,[status(thm)],[c_2103,c_2084])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1262,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_2097,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1262])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1268,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | k2_partfun1(X1_56,X2_56,X0_56,X3_56) = k7_relat_1(X0_56,X3_56) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2092,plain,
    ( k2_partfun1(X0_56,X1_56,X2_56,X3_56) = k7_relat_1(X2_56,X3_56)
    | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
    | v1_funct_1(X2_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1268])).

cnf(c_3424,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_2092])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2548,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_56,X1_56,sK5,X2_56) = k7_relat_1(sK5,X2_56) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_2745,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
    inference(instantiation,[status(thm)],[c_2548])).

cnf(c_3572,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3424,c_29,c_27,c_2745])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1259,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_2100,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_3425,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2092])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2553,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_56,X1_56,sK4,X2_56) = k7_relat_1(sK4,X2_56) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_2758,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(instantiation,[status(thm)],[c_2553])).

cnf(c_3612,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3425,c_32,c_30,c_2758])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f106])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f81])).

cnf(c_24,plain,
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
    inference(cnf_transformation,[],[f82])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_219,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_25,c_24,c_23])).

cnf(c_220,plain,
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
    inference(renaming,[status(thm)],[c_219])).

cnf(c_1249,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56)
    | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
    | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X1_56) = X0_56 ),
    inference(subtyping,[status(esa)],[c_220])).

cnf(c_2110,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1276,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
    | ~ v1_xboole_0(X1_56)
    | v1_xboole_0(X0_56) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2085,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
    | v1_xboole_0(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1276])).

cnf(c_2333,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2110,c_2085])).

cnf(c_9550,plain,
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
    inference(superposition,[status(thm)],[c_3612,c_2333])).

cnf(c_38,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_41,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_42,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_48,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_49,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13036,plain,
    ( v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
    | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9550,c_41,c_42,c_47,c_48,c_49])).

cnf(c_13037,plain,
    ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_13036])).

cnf(c_13050,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3572,c_13037])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_50,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_51,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_52,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_13625,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13050,c_44,c_50,c_51,c_52])).

cnf(c_13635,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2752,c_13625])).

cnf(c_12,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_542,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_543,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_545,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_543,c_37,c_35])).

cnf(c_1248,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_545])).

cnf(c_2111,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1279,plain,
    ( ~ r1_xboole_0(X0_56,X1_56)
    | k1_setfam_1(k2_tarski(X0_56,X1_56)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2083,plain,
    ( k1_setfam_1(k2_tarski(X0_56,X1_56)) = k1_xboole_0
    | r1_xboole_0(X0_56,X1_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1279])).

cnf(c_3122,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2111,c_2083])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_497,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_14,c_18])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_18,c_14,c_13])).

cnf(c_502,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_501])).

cnf(c_555,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_15,c_502])).

cnf(c_559,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_555,c_18,c_15,c_14,c_13])).

cnf(c_560,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_559])).

cnf(c_1247,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | v1_xboole_0(X2_56)
    | k1_relat_1(X0_56) = X1_56 ),
    inference(subtyping,[status(esa)],[c_560])).

cnf(c_2112,plain,
    ( k1_relat_1(X0_56) = X1_56
    | v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | v1_funct_1(X0_56) != iProver_top
    | v1_xboole_0(X2_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1247])).

cnf(c_4253,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_2112])).

cnf(c_2538,plain,
    ( ~ v1_funct_2(sK5,X0_56,X1_56)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_56)
    | k1_relat_1(sK5) = X0_56 ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_2739,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2538])).

cnf(c_4768,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4253,c_38,c_29,c_28,c_27,c_2739])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1270,plain,
    ( ~ r1_xboole_0(X0_56,k1_relat_1(X1_56))
    | ~ v1_relat_1(X1_56)
    | k7_relat_1(X1_56,X0_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_2090,plain,
    ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(X1_56,k1_relat_1(X0_56)) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_4771,plain,
    ( k7_relat_1(sK5,X0_56) = k1_xboole_0
    | r1_xboole_0(X0_56,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4768,c_2090])).

cnf(c_1269,plain,
    ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | v1_relat_1(X0_56) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2453,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2454,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2453])).

cnf(c_5114,plain,
    ( r1_xboole_0(X0_56,sK3) != iProver_top
    | k7_relat_1(sK5,X0_56) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4771,c_52,c_2454])).

cnf(c_5115,plain,
    ( k7_relat_1(sK5,X0_56) = k1_xboole_0
    | r1_xboole_0(X0_56,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5114])).

cnf(c_5122,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2111,c_5115])).

cnf(c_2091,plain,
    ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
    | v1_relat_1(X0_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1269])).

cnf(c_3265,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2097,c_2091])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1275,plain,
    ( ~ v1_relat_1(X0_56)
    | k7_relat_1(X0_56,k1_setfam_1(k2_tarski(X1_56,X2_56))) = k7_relat_1(k7_relat_1(X0_56,X1_56),X2_56) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2086,plain,
    ( k7_relat_1(X0_56,k1_setfam_1(k2_tarski(X1_56,X2_56))) = k7_relat_1(k7_relat_1(X0_56,X1_56),X2_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_3443,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_56,X1_56))) = k7_relat_1(k7_relat_1(sK5,X0_56),X1_56) ),
    inference(superposition,[status(thm)],[c_3265,c_2086])).

cnf(c_3669,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3122,c_3443])).

cnf(c_5124,plain,
    ( k7_relat_1(k1_xboole_0,sK3) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5122,c_3669])).

cnf(c_6,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1274,plain,
    ( k7_relat_1(k1_xboole_0,X0_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_5125,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5124,c_1274])).

cnf(c_13636,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13635,c_3122,c_5125])).

cnf(c_3266,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2091])).

cnf(c_3444,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_56,X1_56))) = k7_relat_1(k7_relat_1(sK4,X0_56),X1_56) ),
    inference(superposition,[status(thm)],[c_3266,c_2086])).

cnf(c_13637,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13636,c_2752,c_3444])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1273,plain,
    ( ~ v1_relat_1(X0_56)
    | k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2087,plain,
    ( k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56)
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_3379,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0_56)) = k9_relat_1(sK5,X0_56) ),
    inference(superposition,[status(thm)],[c_3265,c_2087])).

cnf(c_5128,plain,
    ( k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5122,c_3379])).

cnf(c_5306,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5125,c_3379])).

cnf(c_2,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1278,plain,
    ( k1_setfam_1(k2_tarski(X0_56,k1_xboole_0)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1280,plain,
    ( r1_xboole_0(X0_56,X1_56)
    | k1_setfam_1(k2_tarski(X0_56,X1_56)) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_2082,plain,
    ( k1_setfam_1(k2_tarski(X0_56,X1_56)) != k1_xboole_0
    | r1_xboole_0(X0_56,X1_56) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_3063,plain,
    ( r1_xboole_0(X0_56,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1278,c_2082])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1272,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0_56),X1_56)
    | ~ v1_relat_1(X0_56)
    | k9_relat_1(X0_56,X1_56) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2088,plain,
    ( k9_relat_1(X0_56,X1_56) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_56),X1_56) != iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_3522,plain,
    ( k9_relat_1(X0_56,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_56) != iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_2088])).

cnf(c_4502,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3265,c_3522])).

cnf(c_5307,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5306,c_4502])).

cnf(c_5584,plain,
    ( k9_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5128,c_5307])).

cnf(c_9,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1271,plain,
    ( r1_xboole_0(k1_relat_1(X0_56),X1_56)
    | ~ v1_relat_1(X0_56)
    | k9_relat_1(X0_56,X1_56) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2089,plain,
    ( k9_relat_1(X0_56,X1_56) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0_56),X1_56) = iProver_top
    | v1_relat_1(X0_56) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1271])).

cnf(c_5586,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5584,c_2089])).

cnf(c_5587,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5586,c_4768])).

cnf(c_5590,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5587,c_52,c_2454])).

cnf(c_4254,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2100,c_2112])).

cnf(c_2543,plain,
    ( ~ v1_funct_2(sK4,X0_56,X1_56)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_56)
    | k1_relat_1(sK4) = X0_56 ),
    inference(instantiation,[status(thm)],[c_1247])).

cnf(c_2742,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2543])).

cnf(c_4792,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4254,c_38,c_32,c_31,c_30,c_2742])).

cnf(c_4795,plain,
    ( k7_relat_1(sK4,X0_56) = k1_xboole_0
    | r1_xboole_0(X0_56,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4792,c_2090])).

cnf(c_2456,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_2457,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2456])).

cnf(c_5174,plain,
    ( r1_xboole_0(X0_56,sK2) != iProver_top
    | k7_relat_1(sK4,X0_56) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4795,c_49,c_2457])).

cnf(c_5175,plain,
    ( k7_relat_1(sK4,X0_56) = k1_xboole_0
    | r1_xboole_0(X0_56,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5174])).

cnf(c_5597,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5590,c_5175])).

cnf(c_3931,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0_56),k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1278,c_3444])).

cnf(c_5704,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5597,c_3931])).

cnf(c_5709,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5704,c_1274])).

cnf(c_3930,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3122,c_3444])).

cnf(c_6007,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5709,c_3930])).

cnf(c_13638,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13637,c_6007])).

cnf(c_13639,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13638])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f107])).

cnf(c_212,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_22,c_25,c_24,c_23])).

cnf(c_213,plain,
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
    inference(renaming,[status(thm)],[c_212])).

cnf(c_1250,plain,
    ( ~ v1_funct_2(X0_56,X1_56,X2_56)
    | ~ v1_funct_2(X3_56,X4_56,X2_56)
    | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
    | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
    | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
    | ~ v1_funct_1(X0_56)
    | ~ v1_funct_1(X3_56)
    | v1_xboole_0(X2_56)
    | v1_xboole_0(X1_56)
    | v1_xboole_0(X4_56)
    | v1_xboole_0(X5_56)
    | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
    | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X4_56) = X3_56 ),
    inference(subtyping,[status(esa)],[c_213])).

cnf(c_2109,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_2305,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2109,c_2085])).

cnf(c_8321,plain,
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
    inference(superposition,[status(thm)],[c_3612,c_2305])).

cnf(c_9401,plain,
    ( v1_funct_1(X1_56) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
    | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8321,c_41,c_42,c_47,c_48,c_49])).

cnf(c_9402,plain,
    ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
    | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
    | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
    | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
    | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
    | v1_funct_1(X1_56) != iProver_top
    | v1_xboole_0(X0_56) = iProver_top ),
    inference(renaming,[status(thm)],[c_9401])).

cnf(c_9415,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3572,c_9402])).

cnf(c_10546,plain,
    ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9415,c_44,c_50,c_51,c_52])).

cnf(c_10556,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2752,c_10546])).

cnf(c_10557,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10556,c_3122,c_5125])).

cnf(c_10558,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10557,c_2752,c_3444])).

cnf(c_10559,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10558,c_6007])).

cnf(c_10560,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10559])).

cnf(c_26,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1263,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2940,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2752,c_1263])).

cnf(c_3209,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3122,c_2940])).

cnf(c_3576,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3572,c_3209])).

cnf(c_3941,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3576,c_3612])).

cnf(c_5293,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5125,c_3941])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13639,c_10560,c_5709,c_5293,c_45,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.38/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/1.49  
% 7.38/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.38/1.49  
% 7.38/1.49  ------  iProver source info
% 7.38/1.49  
% 7.38/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.38/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.38/1.49  git: non_committed_changes: false
% 7.38/1.49  git: last_make_outside_of_git: false
% 7.38/1.49  
% 7.38/1.49  ------ 
% 7.38/1.49  
% 7.38/1.49  ------ Input Options
% 7.38/1.49  
% 7.38/1.49  --out_options                           all
% 7.38/1.49  --tptp_safe_out                         true
% 7.38/1.49  --problem_path                          ""
% 7.38/1.49  --include_path                          ""
% 7.38/1.49  --clausifier                            res/vclausify_rel
% 7.38/1.49  --clausifier_options                    --mode clausify
% 7.38/1.49  --stdin                                 false
% 7.38/1.49  --stats_out                             all
% 7.38/1.49  
% 7.38/1.49  ------ General Options
% 7.38/1.49  
% 7.38/1.49  --fof                                   false
% 7.38/1.49  --time_out_real                         305.
% 7.38/1.49  --time_out_virtual                      -1.
% 7.38/1.49  --symbol_type_check                     false
% 7.38/1.49  --clausify_out                          false
% 7.38/1.49  --sig_cnt_out                           false
% 7.38/1.49  --trig_cnt_out                          false
% 7.38/1.49  --trig_cnt_out_tolerance                1.
% 7.38/1.49  --trig_cnt_out_sk_spl                   false
% 7.38/1.49  --abstr_cl_out                          false
% 7.38/1.49  
% 7.38/1.49  ------ Global Options
% 7.38/1.49  
% 7.38/1.49  --schedule                              default
% 7.38/1.49  --add_important_lit                     false
% 7.38/1.49  --prop_solver_per_cl                    1000
% 7.38/1.49  --min_unsat_core                        false
% 7.38/1.49  --soft_assumptions                      false
% 7.38/1.49  --soft_lemma_size                       3
% 7.38/1.49  --prop_impl_unit_size                   0
% 7.38/1.49  --prop_impl_unit                        []
% 7.38/1.49  --share_sel_clauses                     true
% 7.38/1.49  --reset_solvers                         false
% 7.38/1.49  --bc_imp_inh                            [conj_cone]
% 7.38/1.49  --conj_cone_tolerance                   3.
% 7.38/1.49  --extra_neg_conj                        none
% 7.38/1.49  --large_theory_mode                     true
% 7.38/1.49  --prolific_symb_bound                   200
% 7.38/1.49  --lt_threshold                          2000
% 7.38/1.49  --clause_weak_htbl                      true
% 7.38/1.49  --gc_record_bc_elim                     false
% 7.38/1.49  
% 7.38/1.49  ------ Preprocessing Options
% 7.38/1.49  
% 7.38/1.49  --preprocessing_flag                    true
% 7.38/1.49  --time_out_prep_mult                    0.1
% 7.38/1.49  --splitting_mode                        input
% 7.38/1.49  --splitting_grd                         true
% 7.38/1.49  --splitting_cvd                         false
% 7.38/1.49  --splitting_cvd_svl                     false
% 7.38/1.49  --splitting_nvd                         32
% 7.38/1.49  --sub_typing                            true
% 7.38/1.49  --prep_gs_sim                           true
% 7.38/1.49  --prep_unflatten                        true
% 7.38/1.49  --prep_res_sim                          true
% 7.38/1.49  --prep_upred                            true
% 7.38/1.49  --prep_sem_filter                       exhaustive
% 7.38/1.49  --prep_sem_filter_out                   false
% 7.38/1.49  --pred_elim                             true
% 7.38/1.49  --res_sim_input                         true
% 7.38/1.49  --eq_ax_congr_red                       true
% 7.38/1.49  --pure_diseq_elim                       true
% 7.38/1.49  --brand_transform                       false
% 7.38/1.49  --non_eq_to_eq                          false
% 7.38/1.49  --prep_def_merge                        true
% 7.38/1.49  --prep_def_merge_prop_impl              false
% 7.38/1.49  --prep_def_merge_mbd                    true
% 7.38/1.49  --prep_def_merge_tr_red                 false
% 7.38/1.49  --prep_def_merge_tr_cl                  false
% 7.38/1.49  --smt_preprocessing                     true
% 7.38/1.49  --smt_ac_axioms                         fast
% 7.38/1.49  --preprocessed_out                      false
% 7.38/1.49  --preprocessed_stats                    false
% 7.38/1.49  
% 7.38/1.49  ------ Abstraction refinement Options
% 7.38/1.49  
% 7.38/1.49  --abstr_ref                             []
% 7.38/1.49  --abstr_ref_prep                        false
% 7.38/1.49  --abstr_ref_until_sat                   false
% 7.38/1.49  --abstr_ref_sig_restrict                funpre
% 7.38/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.49  --abstr_ref_under                       []
% 7.38/1.49  
% 7.38/1.49  ------ SAT Options
% 7.38/1.49  
% 7.38/1.49  --sat_mode                              false
% 7.38/1.49  --sat_fm_restart_options                ""
% 7.38/1.49  --sat_gr_def                            false
% 7.38/1.49  --sat_epr_types                         true
% 7.38/1.49  --sat_non_cyclic_types                  false
% 7.38/1.49  --sat_finite_models                     false
% 7.38/1.49  --sat_fm_lemmas                         false
% 7.38/1.49  --sat_fm_prep                           false
% 7.38/1.49  --sat_fm_uc_incr                        true
% 7.38/1.49  --sat_out_model                         small
% 7.38/1.49  --sat_out_clauses                       false
% 7.38/1.49  
% 7.38/1.49  ------ QBF Options
% 7.38/1.49  
% 7.38/1.49  --qbf_mode                              false
% 7.38/1.49  --qbf_elim_univ                         false
% 7.38/1.49  --qbf_dom_inst                          none
% 7.38/1.49  --qbf_dom_pre_inst                      false
% 7.38/1.49  --qbf_sk_in                             false
% 7.38/1.49  --qbf_pred_elim                         true
% 7.38/1.49  --qbf_split                             512
% 7.38/1.49  
% 7.38/1.49  ------ BMC1 Options
% 7.38/1.49  
% 7.38/1.49  --bmc1_incremental                      false
% 7.38/1.49  --bmc1_axioms                           reachable_all
% 7.38/1.49  --bmc1_min_bound                        0
% 7.38/1.49  --bmc1_max_bound                        -1
% 7.38/1.49  --bmc1_max_bound_default                -1
% 7.38/1.49  --bmc1_symbol_reachability              true
% 7.38/1.49  --bmc1_property_lemmas                  false
% 7.38/1.49  --bmc1_k_induction                      false
% 7.38/1.49  --bmc1_non_equiv_states                 false
% 7.38/1.49  --bmc1_deadlock                         false
% 7.38/1.49  --bmc1_ucm                              false
% 7.38/1.49  --bmc1_add_unsat_core                   none
% 7.38/1.49  --bmc1_unsat_core_children              false
% 7.38/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.49  --bmc1_out_stat                         full
% 7.38/1.49  --bmc1_ground_init                      false
% 7.38/1.49  --bmc1_pre_inst_next_state              false
% 7.38/1.49  --bmc1_pre_inst_state                   false
% 7.38/1.49  --bmc1_pre_inst_reach_state             false
% 7.38/1.49  --bmc1_out_unsat_core                   false
% 7.38/1.49  --bmc1_aig_witness_out                  false
% 7.38/1.49  --bmc1_verbose                          false
% 7.38/1.49  --bmc1_dump_clauses_tptp                false
% 7.38/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.49  --bmc1_dump_file                        -
% 7.38/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.49  --bmc1_ucm_extend_mode                  1
% 7.38/1.49  --bmc1_ucm_init_mode                    2
% 7.38/1.49  --bmc1_ucm_cone_mode                    none
% 7.38/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.49  --bmc1_ucm_relax_model                  4
% 7.38/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.49  --bmc1_ucm_layered_model                none
% 7.38/1.49  --bmc1_ucm_max_lemma_size               10
% 7.38/1.49  
% 7.38/1.49  ------ AIG Options
% 7.38/1.49  
% 7.38/1.49  --aig_mode                              false
% 7.38/1.49  
% 7.38/1.49  ------ Instantiation Options
% 7.38/1.49  
% 7.38/1.49  --instantiation_flag                    true
% 7.38/1.49  --inst_sos_flag                         false
% 7.38/1.49  --inst_sos_phase                        true
% 7.38/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.49  --inst_lit_sel_side                     num_symb
% 7.38/1.49  --inst_solver_per_active                1400
% 7.38/1.49  --inst_solver_calls_frac                1.
% 7.38/1.49  --inst_passive_queue_type               priority_queues
% 7.38/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.49  --inst_passive_queues_freq              [25;2]
% 7.38/1.49  --inst_dismatching                      true
% 7.38/1.49  --inst_eager_unprocessed_to_passive     true
% 7.38/1.49  --inst_prop_sim_given                   true
% 7.38/1.49  --inst_prop_sim_new                     false
% 7.38/1.49  --inst_subs_new                         false
% 7.38/1.49  --inst_eq_res_simp                      false
% 7.38/1.49  --inst_subs_given                       false
% 7.38/1.49  --inst_orphan_elimination               true
% 7.38/1.49  --inst_learning_loop_flag               true
% 7.38/1.49  --inst_learning_start                   3000
% 7.38/1.49  --inst_learning_factor                  2
% 7.38/1.49  --inst_start_prop_sim_after_learn       3
% 7.38/1.49  --inst_sel_renew                        solver
% 7.38/1.49  --inst_lit_activity_flag                true
% 7.38/1.49  --inst_restr_to_given                   false
% 7.38/1.49  --inst_activity_threshold               500
% 7.38/1.49  --inst_out_proof                        true
% 7.38/1.49  
% 7.38/1.49  ------ Resolution Options
% 7.38/1.49  
% 7.38/1.49  --resolution_flag                       true
% 7.38/1.49  --res_lit_sel                           adaptive
% 7.38/1.49  --res_lit_sel_side                      none
% 7.38/1.49  --res_ordering                          kbo
% 7.38/1.49  --res_to_prop_solver                    active
% 7.38/1.49  --res_prop_simpl_new                    false
% 7.38/1.49  --res_prop_simpl_given                  true
% 7.38/1.49  --res_passive_queue_type                priority_queues
% 7.38/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.49  --res_passive_queues_freq               [15;5]
% 7.38/1.49  --res_forward_subs                      full
% 7.38/1.49  --res_backward_subs                     full
% 7.38/1.49  --res_forward_subs_resolution           true
% 7.38/1.49  --res_backward_subs_resolution          true
% 7.38/1.49  --res_orphan_elimination                true
% 7.38/1.49  --res_time_limit                        2.
% 7.38/1.49  --res_out_proof                         true
% 7.38/1.49  
% 7.38/1.49  ------ Superposition Options
% 7.38/1.49  
% 7.38/1.49  --superposition_flag                    true
% 7.38/1.49  --sup_passive_queue_type                priority_queues
% 7.38/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.49  --demod_completeness_check              fast
% 7.38/1.49  --demod_use_ground                      true
% 7.38/1.49  --sup_to_prop_solver                    passive
% 7.38/1.49  --sup_prop_simpl_new                    true
% 7.38/1.49  --sup_prop_simpl_given                  true
% 7.38/1.49  --sup_fun_splitting                     false
% 7.38/1.49  --sup_smt_interval                      50000
% 7.38/1.49  
% 7.38/1.49  ------ Superposition Simplification Setup
% 7.38/1.49  
% 7.38/1.49  --sup_indices_passive                   []
% 7.38/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.49  --sup_full_bw                           [BwDemod]
% 7.38/1.49  --sup_immed_triv                        [TrivRules]
% 7.38/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.49  --sup_immed_bw_main                     []
% 7.38/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.49  
% 7.38/1.49  ------ Combination Options
% 7.38/1.49  
% 7.38/1.49  --comb_res_mult                         3
% 7.38/1.49  --comb_sup_mult                         2
% 7.38/1.49  --comb_inst_mult                        10
% 7.38/1.49  
% 7.38/1.49  ------ Debug Options
% 7.38/1.49  
% 7.38/1.49  --dbg_backtrace                         false
% 7.38/1.49  --dbg_dump_prop_clauses                 false
% 7.38/1.49  --dbg_dump_prop_clauses_file            -
% 7.38/1.49  --dbg_out_stat                          false
% 7.38/1.49  ------ Parsing...
% 7.38/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.38/1.49  
% 7.38/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.38/1.49  
% 7.38/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.38/1.49  
% 7.38/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.38/1.49  ------ Proving...
% 7.38/1.49  ------ Problem Properties 
% 7.38/1.49  
% 7.38/1.49  
% 7.38/1.49  clauses                                 34
% 7.38/1.49  conjectures                             13
% 7.38/1.49  EPR                                     9
% 7.38/1.49  Horn                                    27
% 7.38/1.49  unary                                   15
% 7.38/1.49  binary                                  6
% 7.38/1.49  lits                                    134
% 7.38/1.49  lits eq                                 21
% 7.38/1.49  fd_pure                                 0
% 7.38/1.49  fd_pseudo                               0
% 7.38/1.49  fd_cond                                 0
% 7.38/1.49  fd_pseudo_cond                          1
% 7.38/1.49  AC symbols                              0
% 7.38/1.49  
% 7.38/1.49  ------ Schedule dynamic 5 is on 
% 7.38/1.49  
% 7.38/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.38/1.49  
% 7.38/1.49  
% 7.38/1.49  ------ 
% 7.38/1.49  Current options:
% 7.38/1.49  ------ 
% 7.38/1.49  
% 7.38/1.49  ------ Input Options
% 7.38/1.49  
% 7.38/1.49  --out_options                           all
% 7.38/1.49  --tptp_safe_out                         true
% 7.38/1.49  --problem_path                          ""
% 7.38/1.49  --include_path                          ""
% 7.38/1.49  --clausifier                            res/vclausify_rel
% 7.38/1.49  --clausifier_options                    --mode clausify
% 7.38/1.49  --stdin                                 false
% 7.38/1.49  --stats_out                             all
% 7.38/1.49  
% 7.38/1.49  ------ General Options
% 7.38/1.49  
% 7.38/1.49  --fof                                   false
% 7.38/1.49  --time_out_real                         305.
% 7.38/1.49  --time_out_virtual                      -1.
% 7.38/1.49  --symbol_type_check                     false
% 7.38/1.49  --clausify_out                          false
% 7.38/1.49  --sig_cnt_out                           false
% 7.38/1.49  --trig_cnt_out                          false
% 7.38/1.49  --trig_cnt_out_tolerance                1.
% 7.38/1.49  --trig_cnt_out_sk_spl                   false
% 7.38/1.49  --abstr_cl_out                          false
% 7.38/1.49  
% 7.38/1.49  ------ Global Options
% 7.38/1.49  
% 7.38/1.49  --schedule                              default
% 7.38/1.49  --add_important_lit                     false
% 7.38/1.49  --prop_solver_per_cl                    1000
% 7.38/1.49  --min_unsat_core                        false
% 7.38/1.49  --soft_assumptions                      false
% 7.38/1.49  --soft_lemma_size                       3
% 7.38/1.49  --prop_impl_unit_size                   0
% 7.38/1.49  --prop_impl_unit                        []
% 7.38/1.49  --share_sel_clauses                     true
% 7.38/1.49  --reset_solvers                         false
% 7.38/1.49  --bc_imp_inh                            [conj_cone]
% 7.38/1.49  --conj_cone_tolerance                   3.
% 7.38/1.49  --extra_neg_conj                        none
% 7.38/1.49  --large_theory_mode                     true
% 7.38/1.49  --prolific_symb_bound                   200
% 7.38/1.49  --lt_threshold                          2000
% 7.38/1.49  --clause_weak_htbl                      true
% 7.38/1.49  --gc_record_bc_elim                     false
% 7.38/1.49  
% 7.38/1.49  ------ Preprocessing Options
% 7.38/1.49  
% 7.38/1.49  --preprocessing_flag                    true
% 7.38/1.49  --time_out_prep_mult                    0.1
% 7.38/1.49  --splitting_mode                        input
% 7.38/1.49  --splitting_grd                         true
% 7.38/1.49  --splitting_cvd                         false
% 7.38/1.49  --splitting_cvd_svl                     false
% 7.38/1.49  --splitting_nvd                         32
% 7.38/1.49  --sub_typing                            true
% 7.38/1.49  --prep_gs_sim                           true
% 7.38/1.49  --prep_unflatten                        true
% 7.38/1.49  --prep_res_sim                          true
% 7.38/1.49  --prep_upred                            true
% 7.38/1.49  --prep_sem_filter                       exhaustive
% 7.38/1.49  --prep_sem_filter_out                   false
% 7.38/1.49  --pred_elim                             true
% 7.38/1.49  --res_sim_input                         true
% 7.38/1.49  --eq_ax_congr_red                       true
% 7.38/1.49  --pure_diseq_elim                       true
% 7.38/1.49  --brand_transform                       false
% 7.38/1.49  --non_eq_to_eq                          false
% 7.38/1.49  --prep_def_merge                        true
% 7.38/1.49  --prep_def_merge_prop_impl              false
% 7.38/1.49  --prep_def_merge_mbd                    true
% 7.38/1.49  --prep_def_merge_tr_red                 false
% 7.38/1.49  --prep_def_merge_tr_cl                  false
% 7.38/1.49  --smt_preprocessing                     true
% 7.38/1.49  --smt_ac_axioms                         fast
% 7.38/1.49  --preprocessed_out                      false
% 7.38/1.49  --preprocessed_stats                    false
% 7.38/1.49  
% 7.38/1.49  ------ Abstraction refinement Options
% 7.38/1.49  
% 7.38/1.49  --abstr_ref                             []
% 7.38/1.49  --abstr_ref_prep                        false
% 7.38/1.49  --abstr_ref_until_sat                   false
% 7.38/1.49  --abstr_ref_sig_restrict                funpre
% 7.38/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.38/1.49  --abstr_ref_under                       []
% 7.38/1.49  
% 7.38/1.49  ------ SAT Options
% 7.38/1.49  
% 7.38/1.49  --sat_mode                              false
% 7.38/1.49  --sat_fm_restart_options                ""
% 7.38/1.49  --sat_gr_def                            false
% 7.38/1.49  --sat_epr_types                         true
% 7.38/1.49  --sat_non_cyclic_types                  false
% 7.38/1.49  --sat_finite_models                     false
% 7.38/1.49  --sat_fm_lemmas                         false
% 7.38/1.49  --sat_fm_prep                           false
% 7.38/1.49  --sat_fm_uc_incr                        true
% 7.38/1.49  --sat_out_model                         small
% 7.38/1.49  --sat_out_clauses                       false
% 7.38/1.49  
% 7.38/1.49  ------ QBF Options
% 7.38/1.49  
% 7.38/1.49  --qbf_mode                              false
% 7.38/1.49  --qbf_elim_univ                         false
% 7.38/1.49  --qbf_dom_inst                          none
% 7.38/1.49  --qbf_dom_pre_inst                      false
% 7.38/1.49  --qbf_sk_in                             false
% 7.38/1.49  --qbf_pred_elim                         true
% 7.38/1.49  --qbf_split                             512
% 7.38/1.49  
% 7.38/1.49  ------ BMC1 Options
% 7.38/1.49  
% 7.38/1.49  --bmc1_incremental                      false
% 7.38/1.49  --bmc1_axioms                           reachable_all
% 7.38/1.49  --bmc1_min_bound                        0
% 7.38/1.49  --bmc1_max_bound                        -1
% 7.38/1.49  --bmc1_max_bound_default                -1
% 7.38/1.49  --bmc1_symbol_reachability              true
% 7.38/1.49  --bmc1_property_lemmas                  false
% 7.38/1.49  --bmc1_k_induction                      false
% 7.38/1.49  --bmc1_non_equiv_states                 false
% 7.38/1.49  --bmc1_deadlock                         false
% 7.38/1.49  --bmc1_ucm                              false
% 7.38/1.49  --bmc1_add_unsat_core                   none
% 7.38/1.49  --bmc1_unsat_core_children              false
% 7.38/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.38/1.49  --bmc1_out_stat                         full
% 7.38/1.49  --bmc1_ground_init                      false
% 7.38/1.49  --bmc1_pre_inst_next_state              false
% 7.38/1.49  --bmc1_pre_inst_state                   false
% 7.38/1.49  --bmc1_pre_inst_reach_state             false
% 7.38/1.49  --bmc1_out_unsat_core                   false
% 7.38/1.49  --bmc1_aig_witness_out                  false
% 7.38/1.49  --bmc1_verbose                          false
% 7.38/1.49  --bmc1_dump_clauses_tptp                false
% 7.38/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.38/1.49  --bmc1_dump_file                        -
% 7.38/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.38/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.38/1.49  --bmc1_ucm_extend_mode                  1
% 7.38/1.49  --bmc1_ucm_init_mode                    2
% 7.38/1.49  --bmc1_ucm_cone_mode                    none
% 7.38/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.38/1.49  --bmc1_ucm_relax_model                  4
% 7.38/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.38/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.38/1.49  --bmc1_ucm_layered_model                none
% 7.38/1.49  --bmc1_ucm_max_lemma_size               10
% 7.38/1.49  
% 7.38/1.49  ------ AIG Options
% 7.38/1.49  
% 7.38/1.49  --aig_mode                              false
% 7.38/1.49  
% 7.38/1.49  ------ Instantiation Options
% 7.38/1.49  
% 7.38/1.49  --instantiation_flag                    true
% 7.38/1.49  --inst_sos_flag                         false
% 7.38/1.49  --inst_sos_phase                        true
% 7.38/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.38/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.38/1.49  --inst_lit_sel_side                     none
% 7.38/1.49  --inst_solver_per_active                1400
% 7.38/1.49  --inst_solver_calls_frac                1.
% 7.38/1.49  --inst_passive_queue_type               priority_queues
% 7.38/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.38/1.49  --inst_passive_queues_freq              [25;2]
% 7.38/1.49  --inst_dismatching                      true
% 7.38/1.49  --inst_eager_unprocessed_to_passive     true
% 7.38/1.49  --inst_prop_sim_given                   true
% 7.38/1.49  --inst_prop_sim_new                     false
% 7.38/1.49  --inst_subs_new                         false
% 7.38/1.49  --inst_eq_res_simp                      false
% 7.38/1.49  --inst_subs_given                       false
% 7.38/1.49  --inst_orphan_elimination               true
% 7.38/1.49  --inst_learning_loop_flag               true
% 7.38/1.49  --inst_learning_start                   3000
% 7.38/1.49  --inst_learning_factor                  2
% 7.38/1.49  --inst_start_prop_sim_after_learn       3
% 7.38/1.49  --inst_sel_renew                        solver
% 7.38/1.49  --inst_lit_activity_flag                true
% 7.38/1.49  --inst_restr_to_given                   false
% 7.38/1.49  --inst_activity_threshold               500
% 7.38/1.49  --inst_out_proof                        true
% 7.38/1.49  
% 7.38/1.49  ------ Resolution Options
% 7.38/1.49  
% 7.38/1.49  --resolution_flag                       false
% 7.38/1.49  --res_lit_sel                           adaptive
% 7.38/1.49  --res_lit_sel_side                      none
% 7.38/1.49  --res_ordering                          kbo
% 7.38/1.49  --res_to_prop_solver                    active
% 7.38/1.49  --res_prop_simpl_new                    false
% 7.38/1.49  --res_prop_simpl_given                  true
% 7.38/1.49  --res_passive_queue_type                priority_queues
% 7.38/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.38/1.49  --res_passive_queues_freq               [15;5]
% 7.38/1.49  --res_forward_subs                      full
% 7.38/1.49  --res_backward_subs                     full
% 7.38/1.49  --res_forward_subs_resolution           true
% 7.38/1.49  --res_backward_subs_resolution          true
% 7.38/1.49  --res_orphan_elimination                true
% 7.38/1.49  --res_time_limit                        2.
% 7.38/1.49  --res_out_proof                         true
% 7.38/1.49  
% 7.38/1.49  ------ Superposition Options
% 7.38/1.49  
% 7.38/1.49  --superposition_flag                    true
% 7.38/1.49  --sup_passive_queue_type                priority_queues
% 7.38/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.38/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.38/1.49  --demod_completeness_check              fast
% 7.38/1.49  --demod_use_ground                      true
% 7.38/1.49  --sup_to_prop_solver                    passive
% 7.38/1.49  --sup_prop_simpl_new                    true
% 7.38/1.49  --sup_prop_simpl_given                  true
% 7.38/1.49  --sup_fun_splitting                     false
% 7.38/1.49  --sup_smt_interval                      50000
% 7.38/1.49  
% 7.38/1.49  ------ Superposition Simplification Setup
% 7.38/1.49  
% 7.38/1.49  --sup_indices_passive                   []
% 7.38/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.38/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.38/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.49  --sup_full_bw                           [BwDemod]
% 7.38/1.49  --sup_immed_triv                        [TrivRules]
% 7.38/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.38/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.49  --sup_immed_bw_main                     []
% 7.38/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.38/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.38/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.38/1.49  
% 7.38/1.49  ------ Combination Options
% 7.38/1.49  
% 7.38/1.49  --comb_res_mult                         3
% 7.38/1.49  --comb_sup_mult                         2
% 7.38/1.49  --comb_inst_mult                        10
% 7.38/1.49  
% 7.38/1.49  ------ Debug Options
% 7.38/1.49  
% 7.38/1.49  --dbg_backtrace                         false
% 7.38/1.49  --dbg_dump_prop_clauses                 false
% 7.38/1.49  --dbg_dump_prop_clauses_file            -
% 7.38/1.49  --dbg_out_stat                          false
% 7.38/1.49  
% 7.38/1.49  
% 7.38/1.49  
% 7.38/1.49  
% 7.38/1.49  ------ Proving...
% 7.38/1.49  
% 7.38/1.49  
% 7.38/1.49  % SZS status Theorem for theBenchmark.p
% 7.38/1.49  
% 7.38/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.38/1.49  
% 7.38/1.49  fof(f19,conjecture,(
% 7.38/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f20,negated_conjecture,(
% 7.38/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.38/1.49    inference(negated_conjecture,[],[f19])).
% 7.38/1.49  
% 7.38/1.49  fof(f42,plain,(
% 7.38/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.38/1.49    inference(ennf_transformation,[],[f20])).
% 7.38/1.49  
% 7.38/1.49  fof(f43,plain,(
% 7.38/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.38/1.49    inference(flattening,[],[f42])).
% 7.38/1.49  
% 7.38/1.49  fof(f55,plain,(
% 7.38/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.38/1.49    introduced(choice_axiom,[])).
% 7.38/1.49  
% 7.38/1.49  fof(f54,plain,(
% 7.38/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.38/1.49    introduced(choice_axiom,[])).
% 7.38/1.49  
% 7.38/1.49  fof(f53,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.38/1.49    introduced(choice_axiom,[])).
% 7.38/1.49  
% 7.38/1.49  fof(f52,plain,(
% 7.38/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.38/1.49    introduced(choice_axiom,[])).
% 7.38/1.49  
% 7.38/1.49  fof(f51,plain,(
% 7.38/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.38/1.49    introduced(choice_axiom,[])).
% 7.38/1.49  
% 7.38/1.49  fof(f50,plain,(
% 7.38/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.38/1.49    introduced(choice_axiom,[])).
% 7.38/1.49  
% 7.38/1.49  fof(f56,plain,(
% 7.38/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.38/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f43,f55,f54,f53,f52,f51,f50])).
% 7.38/1.49  
% 7.38/1.49  fof(f89,plain,(
% 7.38/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f3,axiom,(
% 7.38/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f22,plain,(
% 7.38/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.38/1.49    inference(ennf_transformation,[],[f3])).
% 7.38/1.49  
% 7.38/1.49  fof(f60,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.38/1.49    inference(cnf_transformation,[],[f22])).
% 7.38/1.49  
% 7.38/1.49  fof(f5,axiom,(
% 7.38/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f62,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.38/1.49    inference(cnf_transformation,[],[f5])).
% 7.38/1.49  
% 7.38/1.49  fof(f101,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.38/1.49    inference(definition_unfolding,[],[f60,f62])).
% 7.38/1.49  
% 7.38/1.49  fof(f96,plain,(
% 7.38/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f16,axiom,(
% 7.38/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f36,plain,(
% 7.38/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.38/1.49    inference(ennf_transformation,[],[f16])).
% 7.38/1.49  
% 7.38/1.49  fof(f37,plain,(
% 7.38/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.38/1.49    inference(flattening,[],[f36])).
% 7.38/1.49  
% 7.38/1.49  fof(f77,plain,(
% 7.38/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f37])).
% 7.38/1.49  
% 7.38/1.49  fof(f94,plain,(
% 7.38/1.49    v1_funct_1(sK5)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f93,plain,(
% 7.38/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f91,plain,(
% 7.38/1.49    v1_funct_1(sK4)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f17,axiom,(
% 7.38/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f38,plain,(
% 7.38/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.38/1.49    inference(ennf_transformation,[],[f17])).
% 7.38/1.49  
% 7.38/1.49  fof(f39,plain,(
% 7.38/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.38/1.49    inference(flattening,[],[f38])).
% 7.38/1.49  
% 7.38/1.49  fof(f48,plain,(
% 7.38/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.38/1.49    inference(nnf_transformation,[],[f39])).
% 7.38/1.49  
% 7.38/1.49  fof(f49,plain,(
% 7.38/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.38/1.49    inference(flattening,[],[f48])).
% 7.38/1.49  
% 7.38/1.49  fof(f79,plain,(
% 7.38/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f49])).
% 7.38/1.49  
% 7.38/1.49  fof(f106,plain,(
% 7.38/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(equality_resolution,[],[f79])).
% 7.38/1.49  
% 7.38/1.49  fof(f18,axiom,(
% 7.38/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f40,plain,(
% 7.38/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.38/1.49    inference(ennf_transformation,[],[f18])).
% 7.38/1.49  
% 7.38/1.49  fof(f41,plain,(
% 7.38/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.38/1.49    inference(flattening,[],[f40])).
% 7.38/1.49  
% 7.38/1.49  fof(f81,plain,(
% 7.38/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f41])).
% 7.38/1.49  
% 7.38/1.49  fof(f82,plain,(
% 7.38/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f41])).
% 7.38/1.49  
% 7.38/1.49  fof(f83,plain,(
% 7.38/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f41])).
% 7.38/1.49  
% 7.38/1.49  fof(f4,axiom,(
% 7.38/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f23,plain,(
% 7.38/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.38/1.49    inference(ennf_transformation,[],[f4])).
% 7.38/1.49  
% 7.38/1.49  fof(f61,plain,(
% 7.38/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f23])).
% 7.38/1.49  
% 7.38/1.49  fof(f85,plain,(
% 7.38/1.49    ~v1_xboole_0(sK1)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f86,plain,(
% 7.38/1.49    ~v1_xboole_0(sK2)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f92,plain,(
% 7.38/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f88,plain,(
% 7.38/1.49    ~v1_xboole_0(sK3)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f95,plain,(
% 7.38/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f11,axiom,(
% 7.38/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f28,plain,(
% 7.38/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.38/1.49    inference(ennf_transformation,[],[f11])).
% 7.38/1.49  
% 7.38/1.49  fof(f29,plain,(
% 7.38/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.38/1.49    inference(flattening,[],[f28])).
% 7.38/1.49  
% 7.38/1.49  fof(f46,plain,(
% 7.38/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.38/1.49    inference(nnf_transformation,[],[f29])).
% 7.38/1.49  
% 7.38/1.49  fof(f69,plain,(
% 7.38/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f46])).
% 7.38/1.49  
% 7.38/1.49  fof(f90,plain,(
% 7.38/1.49    r1_subset_1(sK2,sK3)),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f1,axiom,(
% 7.38/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f44,plain,(
% 7.38/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.38/1.49    inference(nnf_transformation,[],[f1])).
% 7.38/1.49  
% 7.38/1.49  fof(f57,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f44])).
% 7.38/1.49  
% 7.38/1.49  fof(f99,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.38/1.49    inference(definition_unfolding,[],[f57,f62])).
% 7.38/1.49  
% 7.38/1.49  fof(f14,axiom,(
% 7.38/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f32,plain,(
% 7.38/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.38/1.49    inference(ennf_transformation,[],[f14])).
% 7.38/1.49  
% 7.38/1.49  fof(f33,plain,(
% 7.38/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.38/1.49    inference(flattening,[],[f32])).
% 7.38/1.49  
% 7.38/1.49  fof(f74,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f33])).
% 7.38/1.49  
% 7.38/1.49  fof(f13,axiom,(
% 7.38/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f21,plain,(
% 7.38/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.38/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.38/1.49  
% 7.38/1.49  fof(f31,plain,(
% 7.38/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.49    inference(ennf_transformation,[],[f21])).
% 7.38/1.49  
% 7.38/1.49  fof(f72,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.49    inference(cnf_transformation,[],[f31])).
% 7.38/1.49  
% 7.38/1.49  fof(f15,axiom,(
% 7.38/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f34,plain,(
% 7.38/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.38/1.49    inference(ennf_transformation,[],[f15])).
% 7.38/1.49  
% 7.38/1.49  fof(f35,plain,(
% 7.38/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.38/1.49    inference(flattening,[],[f34])).
% 7.38/1.49  
% 7.38/1.49  fof(f47,plain,(
% 7.38/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.38/1.49    inference(nnf_transformation,[],[f35])).
% 7.38/1.49  
% 7.38/1.49  fof(f75,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f47])).
% 7.38/1.49  
% 7.38/1.49  fof(f12,axiom,(
% 7.38/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f30,plain,(
% 7.38/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.38/1.49    inference(ennf_transformation,[],[f12])).
% 7.38/1.49  
% 7.38/1.49  fof(f71,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.38/1.49    inference(cnf_transformation,[],[f30])).
% 7.38/1.49  
% 7.38/1.49  fof(f10,axiom,(
% 7.38/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f27,plain,(
% 7.38/1.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.38/1.49    inference(ennf_transformation,[],[f10])).
% 7.38/1.49  
% 7.38/1.49  fof(f68,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f27])).
% 7.38/1.49  
% 7.38/1.49  fof(f6,axiom,(
% 7.38/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f24,plain,(
% 7.38/1.49    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.38/1.49    inference(ennf_transformation,[],[f6])).
% 7.38/1.49  
% 7.38/1.49  fof(f63,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f24])).
% 7.38/1.49  
% 7.38/1.49  fof(f102,plain,(
% 7.38/1.49    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 7.38/1.49    inference(definition_unfolding,[],[f63,f62])).
% 7.38/1.49  
% 7.38/1.49  fof(f7,axiom,(
% 7.38/1.49    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f64,plain,(
% 7.38/1.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f7])).
% 7.38/1.49  
% 7.38/1.49  fof(f8,axiom,(
% 7.38/1.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f25,plain,(
% 7.38/1.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.38/1.49    inference(ennf_transformation,[],[f8])).
% 7.38/1.49  
% 7.38/1.49  fof(f65,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f25])).
% 7.38/1.49  
% 7.38/1.49  fof(f2,axiom,(
% 7.38/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f59,plain,(
% 7.38/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.38/1.49    inference(cnf_transformation,[],[f2])).
% 7.38/1.49  
% 7.38/1.49  fof(f100,plain,(
% 7.38/1.49    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 7.38/1.49    inference(definition_unfolding,[],[f59,f62])).
% 7.38/1.49  
% 7.38/1.49  fof(f58,plain,(
% 7.38/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.38/1.49    inference(cnf_transformation,[],[f44])).
% 7.38/1.49  
% 7.38/1.49  fof(f98,plain,(
% 7.38/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.38/1.49    inference(definition_unfolding,[],[f58,f62])).
% 7.38/1.49  
% 7.38/1.49  fof(f9,axiom,(
% 7.38/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.38/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.38/1.49  
% 7.38/1.49  fof(f26,plain,(
% 7.38/1.49    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.38/1.49    inference(ennf_transformation,[],[f9])).
% 7.38/1.49  
% 7.38/1.49  fof(f45,plain,(
% 7.38/1.49    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.38/1.49    inference(nnf_transformation,[],[f26])).
% 7.38/1.49  
% 7.38/1.49  fof(f67,plain,(
% 7.38/1.49    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f45])).
% 7.38/1.49  
% 7.38/1.49  fof(f66,plain,(
% 7.38/1.49    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f45])).
% 7.38/1.49  
% 7.38/1.49  fof(f78,plain,(
% 7.38/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(cnf_transformation,[],[f49])).
% 7.38/1.49  
% 7.38/1.49  fof(f107,plain,(
% 7.38/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.38/1.49    inference(equality_resolution,[],[f78])).
% 7.38/1.49  
% 7.38/1.49  fof(f97,plain,(
% 7.38/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  fof(f87,plain,(
% 7.38/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.38/1.49    inference(cnf_transformation,[],[f56])).
% 7.38/1.49  
% 7.38/1.49  cnf(c_34,negated_conjecture,
% 7.38/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.38/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1256,negated_conjecture,
% 7.38/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_34]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2103,plain,
% 7.38/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1256]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_3,plain,
% 7.38/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.38/1.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.38/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1277,plain,
% 7.38/1.49      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 7.38/1.49      | k9_subset_1(X1_56,X2_56,X0_56) = k1_setfam_1(k2_tarski(X2_56,X0_56)) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2084,plain,
% 7.38/1.49      ( k9_subset_1(X0_56,X1_56,X2_56) = k1_setfam_1(k2_tarski(X1_56,X2_56))
% 7.38/1.49      | m1_subset_1(X2_56,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1277]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2752,plain,
% 7.38/1.49      ( k9_subset_1(sK0,X0_56,sK3) = k1_setfam_1(k2_tarski(X0_56,sK3)) ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_2103,c_2084]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_27,negated_conjecture,
% 7.38/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.38/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1262,negated_conjecture,
% 7.38/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_27]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2097,plain,
% 7.38/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1262]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_19,plain,
% 7.38/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.38/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1268,plain,
% 7.38/1.49      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.38/1.49      | ~ v1_funct_1(X0_56)
% 7.38/1.49      | k2_partfun1(X1_56,X2_56,X0_56,X3_56) = k7_relat_1(X0_56,X3_56) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2092,plain,
% 7.38/1.49      ( k2_partfun1(X0_56,X1_56,X2_56,X3_56) = k7_relat_1(X2_56,X3_56)
% 7.38/1.49      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.38/1.49      | v1_funct_1(X2_56) != iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1268]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_3424,plain,
% 7.38/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56)
% 7.38/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_2097,c_2092]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_29,negated_conjecture,
% 7.38/1.49      ( v1_funct_1(sK5) ),
% 7.38/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2548,plain,
% 7.38/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.38/1.49      | ~ v1_funct_1(sK5)
% 7.38/1.49      | k2_partfun1(X0_56,X1_56,sK5,X2_56) = k7_relat_1(sK5,X2_56) ),
% 7.38/1.49      inference(instantiation,[status(thm)],[c_1268]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2745,plain,
% 7.38/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.38/1.49      | ~ v1_funct_1(sK5)
% 7.38/1.49      | k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
% 7.38/1.49      inference(instantiation,[status(thm)],[c_2548]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_3572,plain,
% 7.38/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_56) = k7_relat_1(sK5,X0_56) ),
% 7.38/1.49      inference(global_propositional_subsumption,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_3424,c_29,c_27,c_2745]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_30,negated_conjecture,
% 7.38/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.38/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1259,negated_conjecture,
% 7.38/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_30]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2100,plain,
% 7.38/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_3425,plain,
% 7.38/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56)
% 7.38/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_2100,c_2092]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_32,negated_conjecture,
% 7.38/1.49      ( v1_funct_1(sK4) ),
% 7.38/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2553,plain,
% 7.38/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.38/1.49      | ~ v1_funct_1(sK4)
% 7.38/1.49      | k2_partfun1(X0_56,X1_56,sK4,X2_56) = k7_relat_1(sK4,X2_56) ),
% 7.38/1.49      inference(instantiation,[status(thm)],[c_1268]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2758,plain,
% 7.38/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.38/1.49      | ~ v1_funct_1(sK4)
% 7.38/1.49      | k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 7.38/1.49      inference(instantiation,[status(thm)],[c_2553]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_3612,plain,
% 7.38/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_56) = k7_relat_1(sK4,X0_56) ),
% 7.38/1.49      inference(global_propositional_subsumption,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_3425,c_32,c_30,c_2758]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_21,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.38/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | ~ v1_funct_1(X3)
% 7.38/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.38/1.49      | v1_xboole_0(X5)
% 7.38/1.49      | v1_xboole_0(X2)
% 7.38/1.49      | v1_xboole_0(X4)
% 7.38/1.49      | v1_xboole_0(X1)
% 7.38/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.38/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_25,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | ~ v1_funct_1(X3)
% 7.38/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.38/1.49      | v1_xboole_0(X5)
% 7.38/1.49      | v1_xboole_0(X2)
% 7.38/1.49      | v1_xboole_0(X4)
% 7.38/1.49      | v1_xboole_0(X1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_24,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.38/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | ~ v1_funct_1(X3)
% 7.38/1.49      | v1_xboole_0(X5)
% 7.38/1.49      | v1_xboole_0(X2)
% 7.38/1.49      | v1_xboole_0(X4)
% 7.38/1.49      | v1_xboole_0(X1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_23,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | ~ v1_funct_1(X3)
% 7.38/1.49      | v1_xboole_0(X5)
% 7.38/1.49      | v1_xboole_0(X2)
% 7.38/1.49      | v1_xboole_0(X4)
% 7.38/1.49      | v1_xboole_0(X1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_219,plain,
% 7.38/1.49      ( ~ v1_funct_1(X3)
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.49      | v1_xboole_0(X5)
% 7.38/1.49      | v1_xboole_0(X2)
% 7.38/1.49      | v1_xboole_0(X4)
% 7.38/1.49      | v1_xboole_0(X1)
% 7.38/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.38/1.49      inference(global_propositional_subsumption,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_21,c_25,c_24,c_23]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_220,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | ~ v1_funct_1(X3)
% 7.38/1.49      | v1_xboole_0(X1)
% 7.38/1.49      | v1_xboole_0(X2)
% 7.38/1.49      | v1_xboole_0(X4)
% 7.38/1.49      | v1_xboole_0(X5)
% 7.38/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.38/1.49      inference(renaming,[status(thm)],[c_219]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1249,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.38/1.49      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 7.38/1.49      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 7.38/1.49      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 7.38/1.49      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.38/1.49      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 7.38/1.49      | ~ v1_funct_1(X0_56)
% 7.38/1.49      | ~ v1_funct_1(X3_56)
% 7.38/1.49      | v1_xboole_0(X2_56)
% 7.38/1.49      | v1_xboole_0(X1_56)
% 7.38/1.49      | v1_xboole_0(X4_56)
% 7.38/1.49      | v1_xboole_0(X5_56)
% 7.38/1.49      | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X1_56) = X0_56 ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_220]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2110,plain,
% 7.38/1.49      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X0_56) = X2_56
% 7.38/1.49      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 7.38/1.49      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 7.38/1.49      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.38/1.49      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 7.38/1.49      | v1_funct_1(X2_56) != iProver_top
% 7.38/1.49      | v1_funct_1(X5_56) != iProver_top
% 7.38/1.49      | v1_xboole_0(X3_56) = iProver_top
% 7.38/1.49      | v1_xboole_0(X1_56) = iProver_top
% 7.38/1.49      | v1_xboole_0(X4_56) = iProver_top
% 7.38/1.49      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_4,plain,
% 7.38/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.38/1.49      | ~ v1_xboole_0(X1)
% 7.38/1.49      | v1_xboole_0(X0) ),
% 7.38/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1276,plain,
% 7.38/1.49      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(X1_56))
% 7.38/1.49      | ~ v1_xboole_0(X1_56)
% 7.38/1.49      | v1_xboole_0(X0_56) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2085,plain,
% 7.38/1.49      ( m1_subset_1(X0_56,k1_zfmisc_1(X1_56)) != iProver_top
% 7.38/1.49      | v1_xboole_0(X1_56) != iProver_top
% 7.38/1.49      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1276]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2333,plain,
% 7.38/1.49      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X0_56,X4_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X0_56,X4_56))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X3_56,X0_56,X4_56),X1_56,k1_tmap_1(X3_56,X1_56,X0_56,X4_56,X2_56,X5_56),X4_56) = X5_56
% 7.38/1.49      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 7.38/1.49      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 7.38/1.49      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 7.38/1.49      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.38/1.49      | v1_funct_1(X5_56) != iProver_top
% 7.38/1.49      | v1_funct_1(X2_56) != iProver_top
% 7.38/1.49      | v1_xboole_0(X0_56) = iProver_top
% 7.38/1.49      | v1_xboole_0(X1_56) = iProver_top
% 7.38/1.49      | v1_xboole_0(X4_56) = iProver_top ),
% 7.38/1.49      inference(forward_subsumption_resolution,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_2110,c_2085]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_9550,plain,
% 7.38/1.49      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
% 7.38/1.49      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 7.38/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.38/1.49      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 7.38/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.38/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.49      | v1_funct_1(X1_56) != iProver_top
% 7.38/1.49      | v1_funct_1(sK4) != iProver_top
% 7.38/1.49      | v1_xboole_0(X0_56) = iProver_top
% 7.38/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.38/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_3612,c_2333]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_38,negated_conjecture,
% 7.38/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_41,plain,
% 7.38/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_37,negated_conjecture,
% 7.38/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.38/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_42,plain,
% 7.38/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_47,plain,
% 7.38/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_31,negated_conjecture,
% 7.38/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_48,plain,
% 7.38/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_49,plain,
% 7.38/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_13036,plain,
% 7.38/1.49      ( v1_funct_1(X1_56) != iProver_top
% 7.38/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.49      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 7.38/1.49      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
% 7.38/1.49      | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 7.38/1.49      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 7.38/1.49      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.49      inference(global_propositional_subsumption,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_9550,c_41,c_42,c_47,c_48,c_49]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_13037,plain,
% 7.38/1.49      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 7.38/1.49      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),X0_56) = X1_56
% 7.38/1.49      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 7.38/1.49      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 7.38/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.49      | v1_funct_1(X1_56) != iProver_top
% 7.38/1.49      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.49      inference(renaming,[status(thm)],[c_13036]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_13050,plain,
% 7.38/1.49      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.49      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 7.38/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.38/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.38/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
% 7.38/1.49      | v1_funct_1(sK5) != iProver_top
% 7.38/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_3572,c_13037]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_35,negated_conjecture,
% 7.38/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.38/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_44,plain,
% 7.38/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_50,plain,
% 7.38/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_28,negated_conjecture,
% 7.38/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_51,plain,
% 7.38/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_52,plain,
% 7.38/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_13625,plain,
% 7.38/1.49      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.49      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 7.38/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.38/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.38/1.49      inference(global_propositional_subsumption,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_13050,c_44,c_50,c_51,c_52]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_13635,plain,
% 7.38/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.49      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.38/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_2752,c_13625]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_12,plain,
% 7.38/1.49      ( ~ r1_subset_1(X0,X1)
% 7.38/1.49      | r1_xboole_0(X0,X1)
% 7.38/1.49      | v1_xboole_0(X0)
% 7.38/1.49      | v1_xboole_0(X1) ),
% 7.38/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_33,negated_conjecture,
% 7.38/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.38/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_542,plain,
% 7.38/1.49      ( r1_xboole_0(X0,X1)
% 7.38/1.49      | v1_xboole_0(X0)
% 7.38/1.49      | v1_xboole_0(X1)
% 7.38/1.49      | sK3 != X1
% 7.38/1.49      | sK2 != X0 ),
% 7.38/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_543,plain,
% 7.38/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.38/1.49      inference(unflattening,[status(thm)],[c_542]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_545,plain,
% 7.38/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.38/1.49      inference(global_propositional_subsumption,
% 7.38/1.49                [status(thm)],
% 7.38/1.49                [c_543,c_37,c_35]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1248,plain,
% 7.38/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_545]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2111,plain,
% 7.38/1.49      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1248]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1,plain,
% 7.38/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.38/1.49      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.38/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_1279,plain,
% 7.38/1.49      ( ~ r1_xboole_0(X0_56,X1_56)
% 7.38/1.49      | k1_setfam_1(k2_tarski(X0_56,X1_56)) = k1_xboole_0 ),
% 7.38/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_2083,plain,
% 7.38/1.49      ( k1_setfam_1(k2_tarski(X0_56,X1_56)) = k1_xboole_0
% 7.38/1.49      | r1_xboole_0(X0_56,X1_56) != iProver_top ),
% 7.38/1.49      inference(predicate_to_equality,[status(thm)],[c_1279]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_3122,plain,
% 7.38/1.49      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.38/1.49      inference(superposition,[status(thm)],[c_2111,c_2083]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_15,plain,
% 7.38/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.49      | v1_partfun1(X0,X1)
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.49      | ~ v1_funct_1(X0)
% 7.38/1.49      | v1_xboole_0(X2) ),
% 7.38/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_14,plain,
% 7.38/1.49      ( v4_relat_1(X0,X1)
% 7.38/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.38/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.38/1.49  
% 7.38/1.49  cnf(c_18,plain,
% 7.38/1.49      ( ~ v1_partfun1(X0,X1)
% 7.38/1.49      | ~ v4_relat_1(X0,X1)
% 7.38/1.49      | ~ v1_relat_1(X0)
% 7.38/1.49      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_497,plain,
% 7.38/1.50      ( ~ v1_partfun1(X0,X1)
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ v1_relat_1(X0)
% 7.38/1.50      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(resolution,[status(thm)],[c_14,c_18]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_13,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | v1_relat_1(X0) ),
% 7.38/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_501,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ v1_partfun1(X0,X1)
% 7.38/1.50      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_497,c_18,c_14,c_13]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_502,plain,
% 7.38/1.50      ( ~ v1_partfun1(X0,X1)
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_501]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_555,plain,
% 7.38/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | v1_xboole_0(X2)
% 7.38/1.50      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(resolution,[status(thm)],[c_15,c_502]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_559,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | v1_xboole_0(X2)
% 7.38/1.50      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_555,c_18,c_15,c_14,c_13]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_560,plain,
% 7.38/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | v1_xboole_0(X2)
% 7.38/1.50      | k1_relat_1(X0) = X1 ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_559]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1247,plain,
% 7.38/1.50      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.38/1.50      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.38/1.50      | ~ v1_funct_1(X0_56)
% 7.38/1.50      | v1_xboole_0(X2_56)
% 7.38/1.50      | k1_relat_1(X0_56) = X1_56 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_560]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2112,plain,
% 7.38/1.50      ( k1_relat_1(X0_56) = X1_56
% 7.38/1.50      | v1_funct_2(X0_56,X1_56,X2_56) != iProver_top
% 7.38/1.50      | m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 7.38/1.50      | v1_funct_1(X0_56) != iProver_top
% 7.38/1.50      | v1_xboole_0(X2_56) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1247]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4253,plain,
% 7.38/1.50      ( k1_relat_1(sK5) = sK3
% 7.38/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top
% 7.38/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2097,c_2112]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2538,plain,
% 7.38/1.50      ( ~ v1_funct_2(sK5,X0_56,X1_56)
% 7.38/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.38/1.50      | ~ v1_funct_1(sK5)
% 7.38/1.50      | v1_xboole_0(X1_56)
% 7.38/1.50      | k1_relat_1(sK5) = X0_56 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_1247]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2739,plain,
% 7.38/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.38/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.38/1.50      | ~ v1_funct_1(sK5)
% 7.38/1.50      | v1_xboole_0(sK1)
% 7.38/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2538]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4768,plain,
% 7.38/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_4253,c_38,c_29,c_28,c_27,c_2739]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10,plain,
% 7.38/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.38/1.50      | ~ v1_relat_1(X1)
% 7.38/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1270,plain,
% 7.38/1.50      ( ~ r1_xboole_0(X0_56,k1_relat_1(X1_56))
% 7.38/1.50      | ~ v1_relat_1(X1_56)
% 7.38/1.50      | k7_relat_1(X1_56,X0_56) = k1_xboole_0 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2090,plain,
% 7.38/1.50      ( k7_relat_1(X0_56,X1_56) = k1_xboole_0
% 7.38/1.50      | r1_xboole_0(X1_56,k1_relat_1(X0_56)) != iProver_top
% 7.38/1.50      | v1_relat_1(X0_56) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4771,plain,
% 7.38/1.50      ( k7_relat_1(sK5,X0_56) = k1_xboole_0
% 7.38/1.50      | r1_xboole_0(X0_56,sK3) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_4768,c_2090]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1269,plain,
% 7.38/1.50      ( ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.38/1.50      | v1_relat_1(X0_56) ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2453,plain,
% 7.38/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.38/1.50      | v1_relat_1(sK5) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2454,plain,
% 7.38/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.38/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2453]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5114,plain,
% 7.38/1.50      ( r1_xboole_0(X0_56,sK3) != iProver_top
% 7.38/1.50      | k7_relat_1(sK5,X0_56) = k1_xboole_0 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_4771,c_52,c_2454]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5115,plain,
% 7.38/1.50      ( k7_relat_1(sK5,X0_56) = k1_xboole_0
% 7.38/1.50      | r1_xboole_0(X0_56,sK3) != iProver_top ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_5114]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5122,plain,
% 7.38/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2111,c_5115]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2091,plain,
% 7.38/1.50      ( m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56))) != iProver_top
% 7.38/1.50      | v1_relat_1(X0_56) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1269]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3265,plain,
% 7.38/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2097,c_2091]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0)
% 7.38/1.50      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.38/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1275,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0_56)
% 7.38/1.50      | k7_relat_1(X0_56,k1_setfam_1(k2_tarski(X1_56,X2_56))) = k7_relat_1(k7_relat_1(X0_56,X1_56),X2_56) ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2086,plain,
% 7.38/1.50      ( k7_relat_1(X0_56,k1_setfam_1(k2_tarski(X1_56,X2_56))) = k7_relat_1(k7_relat_1(X0_56,X1_56),X2_56)
% 7.38/1.50      | v1_relat_1(X0_56) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3443,plain,
% 7.38/1.50      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_56,X1_56))) = k7_relat_1(k7_relat_1(sK5,X0_56),X1_56) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3265,c_2086]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3669,plain,
% 7.38/1.50      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k7_relat_1(sK5,k1_xboole_0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3122,c_3443]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5124,plain,
% 7.38/1.50      ( k7_relat_1(k1_xboole_0,sK3) = k7_relat_1(sK5,k1_xboole_0) ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_5122,c_3669]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6,plain,
% 7.38/1.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1274,plain,
% 7.38/1.50      ( k7_relat_1(k1_xboole_0,X0_56) = k1_xboole_0 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5125,plain,
% 7.38/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_5124,c_1274]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_13636,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_13635,c_3122,c_5125]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3266,plain,
% 7.38/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2100,c_2091]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3444,plain,
% 7.38/1.50      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_56,X1_56))) = k7_relat_1(k7_relat_1(sK4,X0_56),X1_56) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3266,c_2086]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_13637,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.50      | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_13636,c_2752,c_3444]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_7,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0)
% 7.38/1.50      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.38/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1273,plain,
% 7.38/1.50      ( ~ v1_relat_1(X0_56)
% 7.38/1.50      | k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56) ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2087,plain,
% 7.38/1.50      ( k2_relat_1(k7_relat_1(X0_56,X1_56)) = k9_relat_1(X0_56,X1_56)
% 7.38/1.50      | v1_relat_1(X0_56) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3379,plain,
% 7.38/1.50      ( k2_relat_1(k7_relat_1(sK5,X0_56)) = k9_relat_1(sK5,X0_56) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3265,c_2087]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5128,plain,
% 7.38/1.50      ( k9_relat_1(sK5,sK2) = k2_relat_1(k1_xboole_0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5122,c_3379]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5306,plain,
% 7.38/1.50      ( k9_relat_1(sK5,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5125,c_3379]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2,plain,
% 7.38/1.50      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1278,plain,
% 7.38/1.50      ( k1_setfam_1(k2_tarski(X0_56,k1_xboole_0)) = k1_xboole_0 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_0,plain,
% 7.38/1.50      ( r1_xboole_0(X0,X1)
% 7.38/1.50      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1280,plain,
% 7.38/1.50      ( r1_xboole_0(X0_56,X1_56)
% 7.38/1.50      | k1_setfam_1(k2_tarski(X0_56,X1_56)) != k1_xboole_0 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2082,plain,
% 7.38/1.50      ( k1_setfam_1(k2_tarski(X0_56,X1_56)) != k1_xboole_0
% 7.38/1.50      | r1_xboole_0(X0_56,X1_56) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3063,plain,
% 7.38/1.50      ( r1_xboole_0(X0_56,k1_xboole_0) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1278,c_2082]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_8,plain,
% 7.38/1.50      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.38/1.50      | ~ v1_relat_1(X0)
% 7.38/1.50      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1272,plain,
% 7.38/1.50      ( ~ r1_xboole_0(k1_relat_1(X0_56),X1_56)
% 7.38/1.50      | ~ v1_relat_1(X0_56)
% 7.38/1.50      | k9_relat_1(X0_56,X1_56) = k1_xboole_0 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2088,plain,
% 7.38/1.50      ( k9_relat_1(X0_56,X1_56) = k1_xboole_0
% 7.38/1.50      | r1_xboole_0(k1_relat_1(X0_56),X1_56) != iProver_top
% 7.38/1.50      | v1_relat_1(X0_56) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3522,plain,
% 7.38/1.50      ( k9_relat_1(X0_56,k1_xboole_0) = k1_xboole_0
% 7.38/1.50      | v1_relat_1(X0_56) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3063,c_2088]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4502,plain,
% 7.38/1.50      ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3265,c_3522]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5307,plain,
% 7.38/1.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_5306,c_4502]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5584,plain,
% 7.38/1.50      ( k9_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_5128,c_5307]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_9,plain,
% 7.38/1.50      ( r1_xboole_0(k1_relat_1(X0),X1)
% 7.38/1.50      | ~ v1_relat_1(X0)
% 7.38/1.50      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 7.38/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1271,plain,
% 7.38/1.50      ( r1_xboole_0(k1_relat_1(X0_56),X1_56)
% 7.38/1.50      | ~ v1_relat_1(X0_56)
% 7.38/1.50      | k9_relat_1(X0_56,X1_56) != k1_xboole_0 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_9]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2089,plain,
% 7.38/1.50      ( k9_relat_1(X0_56,X1_56) != k1_xboole_0
% 7.38/1.50      | r1_xboole_0(k1_relat_1(X0_56),X1_56) = iProver_top
% 7.38/1.50      | v1_relat_1(X0_56) != iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1271]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5586,plain,
% 7.38/1.50      ( r1_xboole_0(k1_relat_1(sK5),sK2) = iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5584,c_2089]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5587,plain,
% 7.38/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top
% 7.38/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_5586,c_4768]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5590,plain,
% 7.38/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_5587,c_52,c_2454]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4254,plain,
% 7.38/1.50      ( k1_relat_1(sK4) = sK2
% 7.38/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.38/1.50      | v1_funct_1(sK4) != iProver_top
% 7.38/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2100,c_2112]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2543,plain,
% 7.38/1.50      ( ~ v1_funct_2(sK4,X0_56,X1_56)
% 7.38/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56)))
% 7.38/1.50      | ~ v1_funct_1(sK4)
% 7.38/1.50      | v1_xboole_0(X1_56)
% 7.38/1.50      | k1_relat_1(sK4) = X0_56 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_1247]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2742,plain,
% 7.38/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.38/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.38/1.50      | ~ v1_funct_1(sK4)
% 7.38/1.50      | v1_xboole_0(sK1)
% 7.38/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_2543]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4792,plain,
% 7.38/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_4254,c_38,c_32,c_31,c_30,c_2742]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_4795,plain,
% 7.38/1.50      ( k7_relat_1(sK4,X0_56) = k1_xboole_0
% 7.38/1.50      | r1_xboole_0(X0_56,sK2) != iProver_top
% 7.38/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_4792,c_2090]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2456,plain,
% 7.38/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.38/1.50      | v1_relat_1(sK4) ),
% 7.38/1.50      inference(instantiation,[status(thm)],[c_1269]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2457,plain,
% 7.38/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.38/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_2456]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5174,plain,
% 7.38/1.50      ( r1_xboole_0(X0_56,sK2) != iProver_top
% 7.38/1.50      | k7_relat_1(sK4,X0_56) = k1_xboole_0 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_4795,c_49,c_2457]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5175,plain,
% 7.38/1.50      ( k7_relat_1(sK4,X0_56) = k1_xboole_0
% 7.38/1.50      | r1_xboole_0(X0_56,sK2) != iProver_top ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_5174]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5597,plain,
% 7.38/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5590,c_5175]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3931,plain,
% 7.38/1.50      ( k7_relat_1(k7_relat_1(sK4,X0_56),k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_1278,c_3444]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5704,plain,
% 7.38/1.50      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_5597,c_3931]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5709,plain,
% 7.38/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_5704,c_1274]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3930,plain,
% 7.38/1.50      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k7_relat_1(sK4,k1_xboole_0) ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3122,c_3444]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_6007,plain,
% 7.38/1.50      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_5709,c_3930]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_13638,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.50      | k1_xboole_0 != k1_xboole_0
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_13637,c_6007]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_13639,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(equality_resolution_simp,[status(thm)],[c_13638]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_22,plain,
% 7.38/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.38/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_funct_1(X3)
% 7.38/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.38/1.50      | v1_xboole_0(X5)
% 7.38/1.50      | v1_xboole_0(X2)
% 7.38/1.50      | v1_xboole_0(X4)
% 7.38/1.50      | v1_xboole_0(X1)
% 7.38/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.38/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_212,plain,
% 7.38/1.50      ( ~ v1_funct_1(X3)
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.38/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.50      | v1_xboole_0(X5)
% 7.38/1.50      | v1_xboole_0(X2)
% 7.38/1.50      | v1_xboole_0(X4)
% 7.38/1.50      | v1_xboole_0(X1)
% 7.38/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_22,c_25,c_24,c_23]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_213,plain,
% 7.38/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.38/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.38/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.38/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.38/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.38/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.38/1.50      | ~ v1_funct_1(X0)
% 7.38/1.50      | ~ v1_funct_1(X3)
% 7.38/1.50      | v1_xboole_0(X1)
% 7.38/1.50      | v1_xboole_0(X2)
% 7.38/1.50      | v1_xboole_0(X4)
% 7.38/1.50      | v1_xboole_0(X5)
% 7.38/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_212]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1250,plain,
% 7.38/1.50      ( ~ v1_funct_2(X0_56,X1_56,X2_56)
% 7.38/1.50      | ~ v1_funct_2(X3_56,X4_56,X2_56)
% 7.38/1.50      | ~ m1_subset_1(X4_56,k1_zfmisc_1(X5_56))
% 7.38/1.50      | ~ m1_subset_1(X1_56,k1_zfmisc_1(X5_56))
% 7.38/1.50      | ~ m1_subset_1(X0_56,k1_zfmisc_1(k2_zfmisc_1(X1_56,X2_56)))
% 7.38/1.50      | ~ m1_subset_1(X3_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X2_56)))
% 7.38/1.50      | ~ v1_funct_1(X0_56)
% 7.38/1.50      | ~ v1_funct_1(X3_56)
% 7.38/1.50      | v1_xboole_0(X2_56)
% 7.38/1.50      | v1_xboole_0(X1_56)
% 7.38/1.50      | v1_xboole_0(X4_56)
% 7.38/1.50      | v1_xboole_0(X5_56)
% 7.38/1.50      | k2_partfun1(X1_56,X2_56,X0_56,k9_subset_1(X5_56,X4_56,X1_56)) != k2_partfun1(X4_56,X2_56,X3_56,k9_subset_1(X5_56,X4_56,X1_56))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X5_56,X4_56,X1_56),X2_56,k1_tmap_1(X5_56,X2_56,X4_56,X1_56,X3_56,X0_56),X4_56) = X3_56 ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_213]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2109,plain,
% 7.38/1.50      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X4_56,X0_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X4_56,X0_56))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X3_56,X4_56,X0_56),X1_56,k1_tmap_1(X3_56,X1_56,X4_56,X0_56,X5_56,X2_56),X4_56) = X5_56
% 7.38/1.50      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 7.38/1.50      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 7.38/1.50      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.38/1.50      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 7.38/1.50      | v1_funct_1(X2_56) != iProver_top
% 7.38/1.50      | v1_funct_1(X5_56) != iProver_top
% 7.38/1.50      | v1_xboole_0(X3_56) = iProver_top
% 7.38/1.50      | v1_xboole_0(X1_56) = iProver_top
% 7.38/1.50      | v1_xboole_0(X4_56) = iProver_top
% 7.38/1.50      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2305,plain,
% 7.38/1.50      ( k2_partfun1(X0_56,X1_56,X2_56,k9_subset_1(X3_56,X0_56,X4_56)) != k2_partfun1(X4_56,X1_56,X5_56,k9_subset_1(X3_56,X0_56,X4_56))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X3_56,X0_56,X4_56),X1_56,k1_tmap_1(X3_56,X1_56,X0_56,X4_56,X2_56,X5_56),X0_56) = X2_56
% 7.38/1.50      | v1_funct_2(X5_56,X4_56,X1_56) != iProver_top
% 7.38/1.50      | v1_funct_2(X2_56,X0_56,X1_56) != iProver_top
% 7.38/1.50      | m1_subset_1(X0_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X4_56,k1_zfmisc_1(X3_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X5_56,k1_zfmisc_1(k2_zfmisc_1(X4_56,X1_56))) != iProver_top
% 7.38/1.50      | m1_subset_1(X2_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,X1_56))) != iProver_top
% 7.38/1.50      | v1_funct_1(X5_56) != iProver_top
% 7.38/1.50      | v1_funct_1(X2_56) != iProver_top
% 7.38/1.50      | v1_xboole_0(X0_56) = iProver_top
% 7.38/1.50      | v1_xboole_0(X1_56) = iProver_top
% 7.38/1.50      | v1_xboole_0(X4_56) = iProver_top ),
% 7.38/1.50      inference(forward_subsumption_resolution,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_2109,c_2085]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_8321,plain,
% 7.38/1.50      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
% 7.38/1.50      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 7.38/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.38/1.50      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 7.38/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.50      | v1_funct_1(X1_56) != iProver_top
% 7.38/1.50      | v1_funct_1(sK4) != iProver_top
% 7.38/1.50      | v1_xboole_0(X0_56) = iProver_top
% 7.38/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.38/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3612,c_2305]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_9401,plain,
% 7.38/1.50      ( v1_funct_1(X1_56) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.50      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 7.38/1.50      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
% 7.38/1.50      | k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 7.38/1.50      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 7.38/1.50      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_8321,c_41,c_42,c_47,c_48,c_49]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_9402,plain,
% 7.38/1.50      ( k2_partfun1(X0_56,sK1,X1_56,k9_subset_1(X2_56,sK2,X0_56)) != k7_relat_1(sK4,k9_subset_1(X2_56,sK2,X0_56))
% 7.38/1.50      | k2_partfun1(k4_subset_1(X2_56,sK2,X0_56),sK1,k1_tmap_1(X2_56,sK1,sK2,X0_56,sK4,X1_56),sK2) = sK4
% 7.38/1.50      | v1_funct_2(X1_56,X0_56,sK1) != iProver_top
% 7.38/1.50      | m1_subset_1(X0_56,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(X1_56,k1_zfmisc_1(k2_zfmisc_1(X0_56,sK1))) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_56)) != iProver_top
% 7.38/1.50      | v1_funct_1(X1_56) != iProver_top
% 7.38/1.50      | v1_xboole_0(X0_56) = iProver_top ),
% 7.38/1.50      inference(renaming,[status(thm)],[c_9401]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_9415,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 7.38/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.38/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top
% 7.38/1.50      | v1_funct_1(sK5) != iProver_top
% 7.38/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_3572,c_9402]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10546,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(X0_56,sK2,sK3),sK1,k1_tmap_1(X0_56,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | k7_relat_1(sK4,k9_subset_1(X0_56,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_56,sK2,sK3))
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_56)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_56)) != iProver_top ),
% 7.38/1.50      inference(global_propositional_subsumption,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_9415,c_44,c_50,c_51,c_52]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10556,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(superposition,[status(thm)],[c_2752,c_10546]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10557,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_10556,c_3122,c_5125]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10558,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_10557,c_2752,c_3444]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10559,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | k1_xboole_0 != k1_xboole_0
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(light_normalisation,[status(thm)],[c_10558,c_6007]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_10560,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.38/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.38/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.38/1.50      inference(equality_resolution_simp,[status(thm)],[c_10559]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_26,negated_conjecture,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.38/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_1263,negated_conjecture,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.38/1.50      inference(subtyping,[status(esa)],[c_26]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_2940,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_2752,c_1263]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3209,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_3122,c_2940]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3576,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_3572,c_3209]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_3941,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_3576,c_3612]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_5293,plain,
% 7.38/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.38/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.38/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.38/1.50      inference(demodulation,[status(thm)],[c_5125,c_3941]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_45,plain,
% 7.38/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_36,negated_conjecture,
% 7.38/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.38/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(c_43,plain,
% 7.38/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.38/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.38/1.50  
% 7.38/1.50  cnf(contradiction,plain,
% 7.38/1.50      ( $false ),
% 7.38/1.50      inference(minisat,
% 7.38/1.50                [status(thm)],
% 7.38/1.50                [c_13639,c_10560,c_5709,c_5293,c_45,c_43]) ).
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.38/1.50  
% 7.38/1.50  ------                               Statistics
% 7.38/1.50  
% 7.38/1.50  ------ General
% 7.38/1.50  
% 7.38/1.50  abstr_ref_over_cycles:                  0
% 7.38/1.50  abstr_ref_under_cycles:                 0
% 7.38/1.50  gc_basic_clause_elim:                   0
% 7.38/1.50  forced_gc_time:                         0
% 7.38/1.50  parsing_time:                           0.012
% 7.38/1.50  unif_index_cands_time:                  0.
% 7.38/1.50  unif_index_add_time:                    0.
% 7.38/1.50  orderings_time:                         0.
% 7.38/1.50  out_proof_time:                         0.025
% 7.38/1.50  total_time:                             0.733
% 7.38/1.50  num_of_symbols:                         62
% 7.38/1.50  num_of_terms:                           29870
% 7.38/1.50  
% 7.38/1.50  ------ Preprocessing
% 7.38/1.50  
% 7.38/1.50  num_of_splits:                          0
% 7.38/1.50  num_of_split_atoms:                     0
% 7.38/1.50  num_of_reused_defs:                     0
% 7.38/1.50  num_eq_ax_congr_red:                    17
% 7.38/1.50  num_of_sem_filtered_clauses:            1
% 7.38/1.50  num_of_subtypes:                        3
% 7.38/1.50  monotx_restored_types:                  0
% 7.38/1.50  sat_num_of_epr_types:                   0
% 7.38/1.50  sat_num_of_non_cyclic_types:            0
% 7.38/1.50  sat_guarded_non_collapsed_types:        1
% 7.38/1.50  num_pure_diseq_elim:                    0
% 7.38/1.50  simp_replaced_by:                       0
% 7.38/1.50  res_preprocessed:                       180
% 7.38/1.50  prep_upred:                             0
% 7.38/1.50  prep_unflattend:                        32
% 7.38/1.50  smt_new_axioms:                         0
% 7.38/1.50  pred_elim_cands:                        6
% 7.38/1.50  pred_elim:                              3
% 7.38/1.50  pred_elim_cl:                           5
% 7.38/1.50  pred_elim_cycles:                       7
% 7.38/1.50  merged_defs:                            8
% 7.38/1.50  merged_defs_ncl:                        0
% 7.38/1.50  bin_hyper_res:                          8
% 7.38/1.50  prep_cycles:                            4
% 7.38/1.50  pred_elim_time:                         0.01
% 7.38/1.50  splitting_time:                         0.
% 7.38/1.50  sem_filter_time:                        0.
% 7.38/1.50  monotx_time:                            0.
% 7.38/1.50  subtype_inf_time:                       0.002
% 7.38/1.50  
% 7.38/1.50  ------ Problem properties
% 7.38/1.50  
% 7.38/1.50  clauses:                                34
% 7.38/1.50  conjectures:                            13
% 7.38/1.50  epr:                                    9
% 7.38/1.50  horn:                                   27
% 7.38/1.50  ground:                                 14
% 7.38/1.50  unary:                                  15
% 7.38/1.50  binary:                                 6
% 7.38/1.50  lits:                                   134
% 7.38/1.50  lits_eq:                                21
% 7.38/1.50  fd_pure:                                0
% 7.38/1.50  fd_pseudo:                              0
% 7.38/1.50  fd_cond:                                0
% 7.38/1.50  fd_pseudo_cond:                         1
% 7.38/1.50  ac_symbols:                             0
% 7.38/1.50  
% 7.38/1.50  ------ Propositional Solver
% 7.38/1.50  
% 7.38/1.50  prop_solver_calls:                      29
% 7.38/1.50  prop_fast_solver_calls:                 2076
% 7.38/1.50  smt_solver_calls:                       0
% 7.38/1.50  smt_fast_solver_calls:                  0
% 7.38/1.50  prop_num_of_clauses:                    6322
% 7.38/1.50  prop_preprocess_simplified:             13407
% 7.38/1.50  prop_fo_subsumed:                       97
% 7.38/1.50  prop_solver_time:                       0.
% 7.38/1.50  smt_solver_time:                        0.
% 7.38/1.50  smt_fast_solver_time:                   0.
% 7.38/1.50  prop_fast_solver_time:                  0.
% 7.38/1.50  prop_unsat_core_time:                   0.
% 7.38/1.50  
% 7.38/1.50  ------ QBF
% 7.38/1.50  
% 7.38/1.50  qbf_q_res:                              0
% 7.38/1.50  qbf_num_tautologies:                    0
% 7.38/1.50  qbf_prep_cycles:                        0
% 7.38/1.50  
% 7.38/1.50  ------ BMC1
% 7.38/1.50  
% 7.38/1.50  bmc1_current_bound:                     -1
% 7.38/1.50  bmc1_last_solved_bound:                 -1
% 7.38/1.50  bmc1_unsat_core_size:                   -1
% 7.38/1.50  bmc1_unsat_core_parents_size:           -1
% 7.38/1.50  bmc1_merge_next_fun:                    0
% 7.38/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.38/1.50  
% 7.38/1.50  ------ Instantiation
% 7.38/1.50  
% 7.38/1.50  inst_num_of_clauses:                    1687
% 7.38/1.50  inst_num_in_passive:                    236
% 7.38/1.50  inst_num_in_active:                     673
% 7.38/1.50  inst_num_in_unprocessed:                778
% 7.38/1.50  inst_num_of_loops:                      690
% 7.38/1.50  inst_num_of_learning_restarts:          0
% 7.38/1.50  inst_num_moves_active_passive:          12
% 7.38/1.50  inst_lit_activity:                      0
% 7.38/1.50  inst_lit_activity_moves:                0
% 7.38/1.50  inst_num_tautologies:                   0
% 7.38/1.50  inst_num_prop_implied:                  0
% 7.38/1.50  inst_num_existing_simplified:           0
% 7.38/1.50  inst_num_eq_res_simplified:             0
% 7.38/1.50  inst_num_child_elim:                    0
% 7.38/1.50  inst_num_of_dismatching_blockings:      193
% 7.38/1.50  inst_num_of_non_proper_insts:           1319
% 7.38/1.50  inst_num_of_duplicates:                 0
% 7.38/1.50  inst_inst_num_from_inst_to_res:         0
% 7.38/1.50  inst_dismatching_checking_time:         0.
% 7.38/1.50  
% 7.38/1.50  ------ Resolution
% 7.38/1.50  
% 7.38/1.50  res_num_of_clauses:                     0
% 7.38/1.50  res_num_in_passive:                     0
% 7.38/1.50  res_num_in_active:                      0
% 7.38/1.50  res_num_of_loops:                       184
% 7.38/1.50  res_forward_subset_subsumed:            48
% 7.38/1.50  res_backward_subset_subsumed:           4
% 7.38/1.50  res_forward_subsumed:                   0
% 7.38/1.50  res_backward_subsumed:                  0
% 7.38/1.50  res_forward_subsumption_resolution:     1
% 7.38/1.50  res_backward_subsumption_resolution:    0
% 7.38/1.50  res_clause_to_clause_subsumption:       644
% 7.38/1.50  res_orphan_elimination:                 0
% 7.38/1.50  res_tautology_del:                      53
% 7.38/1.50  res_num_eq_res_simplified:              0
% 7.38/1.50  res_num_sel_changes:                    0
% 7.38/1.50  res_moves_from_active_to_pass:          0
% 7.38/1.50  
% 7.38/1.50  ------ Superposition
% 7.38/1.50  
% 7.38/1.50  sup_time_total:                         0.
% 7.38/1.50  sup_time_generating:                    0.
% 7.38/1.50  sup_time_sim_full:                      0.
% 7.38/1.50  sup_time_sim_immed:                     0.
% 7.38/1.50  
% 7.38/1.50  sup_num_of_clauses:                     167
% 7.38/1.50  sup_num_in_active:                      127
% 7.38/1.50  sup_num_in_passive:                     40
% 7.38/1.50  sup_num_of_loops:                       136
% 7.38/1.50  sup_fw_superposition:                   218
% 7.38/1.50  sup_bw_superposition:                   115
% 7.38/1.50  sup_immediate_simplified:               130
% 7.38/1.50  sup_given_eliminated:                   0
% 7.38/1.50  comparisons_done:                       0
% 7.38/1.50  comparisons_avoided:                    0
% 7.38/1.50  
% 7.38/1.50  ------ Simplifications
% 7.38/1.50  
% 7.38/1.50  
% 7.38/1.50  sim_fw_subset_subsumed:                 4
% 7.38/1.50  sim_bw_subset_subsumed:                 0
% 7.38/1.50  sim_fw_subsumed:                        26
% 7.38/1.50  sim_bw_subsumed:                        0
% 7.38/1.50  sim_fw_subsumption_res:                 6
% 7.38/1.50  sim_bw_subsumption_res:                 0
% 7.38/1.50  sim_tautology_del:                      0
% 7.38/1.50  sim_eq_tautology_del:                   21
% 7.38/1.50  sim_eq_res_simp:                        16
% 7.38/1.50  sim_fw_demodulated:                     45
% 7.38/1.50  sim_bw_demodulated:                     10
% 7.38/1.50  sim_light_normalised:                   104
% 7.38/1.50  sim_joinable_taut:                      0
% 7.38/1.50  sim_joinable_simp:                      0
% 7.38/1.50  sim_ac_normalised:                      0
% 7.38/1.50  sim_smt_subsumption:                    0
% 7.38/1.50  
%------------------------------------------------------------------------------
