%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:33 EST 2020

% Result     : Theorem 27.43s
% Output     : CNFRefutation 27.58s
% Verified   : 
% Statistics : Number of formulae       :  281 (6347 expanded)
%              Number of clauses        :  195 (1751 expanded)
%              Number of leaves         :   22 (2121 expanded)
%              Depth                    :   30
%              Number of atoms          : 1423 (66356 expanded)
%              Number of equality atoms :  599 (15072 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f41,f52,f51,f50,f49,f48,f47])).

fof(f83,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f81,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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

fof(f74,plain,(
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

fof(f76,plain,(
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

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f75,plain,(
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

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
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
    inference(equality_resolution,[],[f72])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1057,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1865,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1071,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_subset_1(X1_53,X0_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1852,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_subset_1(X1_53,X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1071])).

cnf(c_3591,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_1852])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_43,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2109,plain,
    ( ~ r1_subset_1(X0_53,sK3)
    | r1_subset_1(sK3,X0_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1071])).

cnf(c_2121,plain,
    ( r1_subset_1(X0_53,sK3) != iProver_top
    | r1_subset_1(sK3,X0_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_2123,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2121])).

cnf(c_3611,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3591,c_39,c_41,c_43,c_2123])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1072,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_xboole_0(X0_53,X1_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1851,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X0_53,X1_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1072])).

cnf(c_3616,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3611,c_1851])).

cnf(c_2065,plain,
    ( ~ r1_subset_1(X0_53,sK2)
    | r1_xboole_0(X0_53,sK2)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_2256,plain,
    ( ~ r1_subset_1(sK3,sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_2260,plain,
    ( r1_subset_1(sK3,sK2) != iProver_top
    | r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2256])).

cnf(c_3674,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3616,c_39,c_41,c_43,c_2123,c_2260])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1079,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1845,plain,
    ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1079])).

cnf(c_3678,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3674,c_1845])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1063,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1859,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1063])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_465,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_15,c_11,c_10])).

cnf(c_470,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_469])).

cnf(c_540,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_470])).

cnf(c_544,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_540,c_15,c_12,c_11,c_10])).

cnf(c_545,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_544])).

cnf(c_1048,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_545])).

cnf(c_1874,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1048])).

cnf(c_6844,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_1874])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1976,plain,
    ( ~ v1_funct_2(X0_53,X1_53,sK1)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(sK1)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_2275,plain,
    ( ~ v1_funct_2(sK5,X0_53,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_2650,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2275])).

cnf(c_6987,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6844,c_35,c_26,c_25,c_24,c_2650])).

cnf(c_1070,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1853,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1070])).

cnf(c_3216,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_1853])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1074,plain,
    ( ~ v1_relat_1(X0_53)
    | k1_relat_1(k7_relat_1(X0_53,X1_53)) = k3_xboole_0(k1_relat_1(X0_53),X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1849,plain,
    ( k1_relat_1(k7_relat_1(X0_53,X1_53)) = k3_xboole_0(k1_relat_1(X0_53),X1_53)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1074])).

cnf(c_3352,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0_53)) = k3_xboole_0(k1_relat_1(sK5),X0_53) ),
    inference(superposition,[status(thm)],[c_3216,c_1849])).

cnf(c_6990,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0_53)) = k3_xboole_0(sK3,X0_53) ),
    inference(demodulation,[status(thm)],[c_6987,c_3352])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1075,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1848,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_7089,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0_53),X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k3_xboole_0(sK3,X0_53)) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,X0_53)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6990,c_1848])).

cnf(c_7384,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK2),X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_7089])).

cnf(c_3477,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1865,c_1851])).

cnf(c_2110,plain,
    ( ~ r1_subset_1(X0_53,sK3)
    | r1_xboole_0(X0_53,sK3)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_2117,plain,
    ( r1_subset_1(X0_53,sK3) != iProver_top
    | r1_xboole_0(X0_53,sK3) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2110])).

cnf(c_2119,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_3594,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3477,c_39,c_41,c_43,c_2119])).

cnf(c_6994,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6987,c_1848])).

cnf(c_7140,plain,
    ( r1_xboole_0(X0_53,sK3) != iProver_top
    | k7_relat_1(sK5,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6994,c_3216])).

cnf(c_7141,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7140])).

cnf(c_7146,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3594,c_7141])).

cnf(c_7385,plain,
    ( k7_relat_1(k1_xboole_0,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7384,c_7146])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1078,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1080,plain,
    ( r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3030,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0)
    | k3_xboole_0(X0_53,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1080])).

cnf(c_3031,plain,
    ( k3_xboole_0(X0_53,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3030])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1076,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1847,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1076])).

cnf(c_3218,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1853])).

cnf(c_46088,plain,
    ( k7_relat_1(k1_xboole_0,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7385,c_1078,c_3031,c_3218])).

cnf(c_7215,plain,
    ( k3_xboole_0(sK3,sK2) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7146,c_6990])).

cnf(c_7216,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7215,c_3678])).

cnf(c_3354,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0_53)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0_53) ),
    inference(superposition,[status(thm)],[c_3218,c_1849])).

cnf(c_37541,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0_53)) = k3_xboole_0(k1_xboole_0,X0_53) ),
    inference(demodulation,[status(thm)],[c_7216,c_3354])).

cnf(c_46093,plain,
    ( k3_xboole_0(k1_xboole_0,X0_53) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_46088,c_37541])).

cnf(c_46098,plain,
    ( k3_xboole_0(k1_xboole_0,X0_53) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_46093,c_7216])).

cnf(c_1844,plain,
    ( k3_xboole_0(X0_53,X1_53) != k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1080])).

cnf(c_46438,plain,
    ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_46098,c_1844])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1060,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1862,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_6845,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1874])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2280,plain,
    ( ~ v1_funct_2(sK4,X0_53,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_2282,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2280])).

cnf(c_7075,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6845,c_35,c_29,c_28,c_27,c_2282])).

cnf(c_7082,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7075,c_1848])).

cnf(c_3217,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1853])).

cnf(c_7218,plain,
    ( r1_xboole_0(X0_53,sK2) != iProver_top
    | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7082,c_3217])).

cnf(c_7219,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7218])).

cnf(c_46649,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_46438,c_7219])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1056,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1866,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1056])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_1065,plain,
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
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1858,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1065])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_1067,plain,
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
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1856,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1069,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1854,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1069])).

cnf(c_3882,plain,
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
    inference(superposition,[status(thm)],[c_1856,c_1854])).

cnf(c_8171,plain,
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
    inference(superposition,[status(thm)],[c_1858,c_3882])).

cnf(c_15369,plain,
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
    inference(superposition,[status(thm)],[c_1859,c_8171])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15586,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15369,c_38,c_41,c_47,c_48])).

cnf(c_15587,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_15586])).

cnf(c_15593,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_15587])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15809,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15593,c_39,c_44,c_45])).

cnf(c_15810,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_15809])).

cnf(c_15815,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1866,c_15810])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_15878,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15815,c_37,c_40])).

cnf(c_3774,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_1854])).

cnf(c_3988,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3774,c_47])).

cnf(c_3598,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3594,c_1845])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1077,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1846,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1077])).

cnf(c_2665,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1866,c_1846])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1064,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2856,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2665,c_1064])).

cnf(c_3618,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3598,c_2856])).

cnf(c_3991,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3988,c_3618])).

cnf(c_3775,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1862,c_1854])).

cnf(c_3993,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3775,c_44])).

cnf(c_4039,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3991,c_3993])).

cnf(c_15881,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_15878,c_4039])).

cnf(c_15882,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_15881,c_15878])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f95])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_198,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_22,c_21,c_20])).

cnf(c_199,plain,
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
    inference(renaming,[status(thm)],[c_198])).

cnf(c_1050,plain,
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
    inference(subtyping,[status(esa)],[c_199])).

cnf(c_1872,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1050])).

cnf(c_4342,plain,
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
    inference(superposition,[status(thm)],[c_3988,c_1872])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4951,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4342,c_38,c_41,c_47,c_48,c_49])).

cnf(c_4952,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_4951])).

cnf(c_4958,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3993,c_4952])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5060,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4958,c_39,c_44,c_45,c_46])).

cnf(c_5061,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_5060])).

cnf(c_5066,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2665,c_5061])).

cnf(c_5067,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5066,c_3598])).

cnf(c_5068,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5067,c_2665])).

cnf(c_5069,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5068,c_3598])).

cnf(c_5070,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5069])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_205,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_22,c_21,c_20])).

cnf(c_206,plain,
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
    inference(renaming,[status(thm)],[c_205])).

cnf(c_1049,plain,
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
    inference(subtyping,[status(esa)],[c_206])).

cnf(c_1873,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1049])).

cnf(c_5206,plain,
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
    inference(superposition,[status(thm)],[c_3988,c_1873])).

cnf(c_10447,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5206,c_38,c_41,c_47,c_48,c_49])).

cnf(c_10448,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_10447])).

cnf(c_10454,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3993,c_10448])).

cnf(c_10494,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10454,c_39,c_44,c_45,c_46])).

cnf(c_10495,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_10494])).

cnf(c_10500,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2665,c_10495])).

cnf(c_10501,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10500,c_3598])).

cnf(c_10502,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10501,c_2665])).

cnf(c_10503,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10502,c_3598])).

cnf(c_10504,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_10503])).

cnf(c_17467,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15882,c_36,c_33,c_31,c_4039,c_5070,c_10504])).

cnf(c_46863,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_46649,c_17467])).

cnf(c_46650,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_46438,c_7141])).

cnf(c_46868,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_46863,c_46650])).

cnf(c_46869,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_46868])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 27.43/4.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.43/4.02  
% 27.43/4.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.43/4.02  
% 27.43/4.02  ------  iProver source info
% 27.43/4.02  
% 27.43/4.02  git: date: 2020-06-30 10:37:57 +0100
% 27.43/4.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.43/4.02  git: non_committed_changes: false
% 27.43/4.02  git: last_make_outside_of_git: false
% 27.43/4.02  
% 27.43/4.02  ------ 
% 27.43/4.02  
% 27.43/4.02  ------ Input Options
% 27.43/4.02  
% 27.43/4.02  --out_options                           all
% 27.43/4.02  --tptp_safe_out                         true
% 27.43/4.02  --problem_path                          ""
% 27.43/4.02  --include_path                          ""
% 27.43/4.02  --clausifier                            res/vclausify_rel
% 27.43/4.02  --clausifier_options                    ""
% 27.43/4.02  --stdin                                 false
% 27.43/4.02  --stats_out                             all
% 27.43/4.02  
% 27.43/4.02  ------ General Options
% 27.43/4.02  
% 27.43/4.02  --fof                                   false
% 27.43/4.02  --time_out_real                         305.
% 27.43/4.02  --time_out_virtual                      -1.
% 27.43/4.02  --symbol_type_check                     false
% 27.43/4.02  --clausify_out                          false
% 27.43/4.02  --sig_cnt_out                           false
% 27.43/4.02  --trig_cnt_out                          false
% 27.43/4.02  --trig_cnt_out_tolerance                1.
% 27.43/4.02  --trig_cnt_out_sk_spl                   false
% 27.43/4.02  --abstr_cl_out                          false
% 27.43/4.02  
% 27.43/4.02  ------ Global Options
% 27.43/4.02  
% 27.43/4.02  --schedule                              default
% 27.43/4.02  --add_important_lit                     false
% 27.43/4.02  --prop_solver_per_cl                    1000
% 27.43/4.02  --min_unsat_core                        false
% 27.43/4.02  --soft_assumptions                      false
% 27.43/4.02  --soft_lemma_size                       3
% 27.43/4.02  --prop_impl_unit_size                   0
% 27.43/4.02  --prop_impl_unit                        []
% 27.43/4.02  --share_sel_clauses                     true
% 27.43/4.02  --reset_solvers                         false
% 27.43/4.02  --bc_imp_inh                            [conj_cone]
% 27.43/4.02  --conj_cone_tolerance                   3.
% 27.43/4.02  --extra_neg_conj                        none
% 27.43/4.02  --large_theory_mode                     true
% 27.43/4.02  --prolific_symb_bound                   200
% 27.43/4.02  --lt_threshold                          2000
% 27.43/4.02  --clause_weak_htbl                      true
% 27.43/4.02  --gc_record_bc_elim                     false
% 27.43/4.02  
% 27.43/4.02  ------ Preprocessing Options
% 27.43/4.02  
% 27.43/4.02  --preprocessing_flag                    true
% 27.43/4.02  --time_out_prep_mult                    0.1
% 27.43/4.02  --splitting_mode                        input
% 27.43/4.02  --splitting_grd                         true
% 27.43/4.02  --splitting_cvd                         false
% 27.43/4.02  --splitting_cvd_svl                     false
% 27.43/4.02  --splitting_nvd                         32
% 27.43/4.02  --sub_typing                            true
% 27.43/4.02  --prep_gs_sim                           true
% 27.43/4.02  --prep_unflatten                        true
% 27.43/4.02  --prep_res_sim                          true
% 27.43/4.02  --prep_upred                            true
% 27.43/4.02  --prep_sem_filter                       exhaustive
% 27.43/4.02  --prep_sem_filter_out                   false
% 27.43/4.02  --pred_elim                             true
% 27.43/4.02  --res_sim_input                         true
% 27.43/4.02  --eq_ax_congr_red                       true
% 27.43/4.02  --pure_diseq_elim                       true
% 27.43/4.02  --brand_transform                       false
% 27.43/4.02  --non_eq_to_eq                          false
% 27.43/4.02  --prep_def_merge                        true
% 27.43/4.02  --prep_def_merge_prop_impl              false
% 27.43/4.02  --prep_def_merge_mbd                    true
% 27.43/4.02  --prep_def_merge_tr_red                 false
% 27.43/4.02  --prep_def_merge_tr_cl                  false
% 27.43/4.02  --smt_preprocessing                     true
% 27.43/4.02  --smt_ac_axioms                         fast
% 27.43/4.02  --preprocessed_out                      false
% 27.43/4.02  --preprocessed_stats                    false
% 27.43/4.02  
% 27.43/4.02  ------ Abstraction refinement Options
% 27.43/4.02  
% 27.43/4.02  --abstr_ref                             []
% 27.43/4.02  --abstr_ref_prep                        false
% 27.43/4.02  --abstr_ref_until_sat                   false
% 27.43/4.02  --abstr_ref_sig_restrict                funpre
% 27.43/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.43/4.02  --abstr_ref_under                       []
% 27.43/4.02  
% 27.43/4.02  ------ SAT Options
% 27.43/4.02  
% 27.43/4.02  --sat_mode                              false
% 27.43/4.02  --sat_fm_restart_options                ""
% 27.43/4.02  --sat_gr_def                            false
% 27.43/4.02  --sat_epr_types                         true
% 27.43/4.02  --sat_non_cyclic_types                  false
% 27.43/4.02  --sat_finite_models                     false
% 27.43/4.02  --sat_fm_lemmas                         false
% 27.43/4.02  --sat_fm_prep                           false
% 27.43/4.02  --sat_fm_uc_incr                        true
% 27.43/4.02  --sat_out_model                         small
% 27.43/4.02  --sat_out_clauses                       false
% 27.43/4.02  
% 27.43/4.02  ------ QBF Options
% 27.43/4.02  
% 27.43/4.02  --qbf_mode                              false
% 27.43/4.02  --qbf_elim_univ                         false
% 27.43/4.02  --qbf_dom_inst                          none
% 27.43/4.02  --qbf_dom_pre_inst                      false
% 27.43/4.02  --qbf_sk_in                             false
% 27.43/4.02  --qbf_pred_elim                         true
% 27.43/4.02  --qbf_split                             512
% 27.43/4.02  
% 27.43/4.02  ------ BMC1 Options
% 27.43/4.02  
% 27.43/4.02  --bmc1_incremental                      false
% 27.43/4.02  --bmc1_axioms                           reachable_all
% 27.43/4.02  --bmc1_min_bound                        0
% 27.43/4.02  --bmc1_max_bound                        -1
% 27.43/4.02  --bmc1_max_bound_default                -1
% 27.43/4.02  --bmc1_symbol_reachability              true
% 27.43/4.02  --bmc1_property_lemmas                  false
% 27.43/4.02  --bmc1_k_induction                      false
% 27.43/4.02  --bmc1_non_equiv_states                 false
% 27.43/4.02  --bmc1_deadlock                         false
% 27.43/4.02  --bmc1_ucm                              false
% 27.43/4.02  --bmc1_add_unsat_core                   none
% 27.43/4.02  --bmc1_unsat_core_children              false
% 27.43/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.43/4.02  --bmc1_out_stat                         full
% 27.43/4.02  --bmc1_ground_init                      false
% 27.43/4.02  --bmc1_pre_inst_next_state              false
% 27.43/4.02  --bmc1_pre_inst_state                   false
% 27.43/4.02  --bmc1_pre_inst_reach_state             false
% 27.43/4.02  --bmc1_out_unsat_core                   false
% 27.43/4.02  --bmc1_aig_witness_out                  false
% 27.43/4.02  --bmc1_verbose                          false
% 27.43/4.02  --bmc1_dump_clauses_tptp                false
% 27.43/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.43/4.02  --bmc1_dump_file                        -
% 27.43/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.43/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.43/4.02  --bmc1_ucm_extend_mode                  1
% 27.43/4.02  --bmc1_ucm_init_mode                    2
% 27.43/4.02  --bmc1_ucm_cone_mode                    none
% 27.43/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.43/4.02  --bmc1_ucm_relax_model                  4
% 27.43/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.43/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.43/4.02  --bmc1_ucm_layered_model                none
% 27.43/4.02  --bmc1_ucm_max_lemma_size               10
% 27.43/4.02  
% 27.43/4.02  ------ AIG Options
% 27.43/4.02  
% 27.43/4.02  --aig_mode                              false
% 27.43/4.02  
% 27.43/4.02  ------ Instantiation Options
% 27.43/4.02  
% 27.43/4.02  --instantiation_flag                    true
% 27.43/4.02  --inst_sos_flag                         true
% 27.43/4.02  --inst_sos_phase                        true
% 27.43/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.43/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.43/4.02  --inst_lit_sel_side                     num_symb
% 27.43/4.02  --inst_solver_per_active                1400
% 27.43/4.02  --inst_solver_calls_frac                1.
% 27.43/4.02  --inst_passive_queue_type               priority_queues
% 27.43/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.43/4.02  --inst_passive_queues_freq              [25;2]
% 27.43/4.02  --inst_dismatching                      true
% 27.43/4.02  --inst_eager_unprocessed_to_passive     true
% 27.43/4.02  --inst_prop_sim_given                   true
% 27.43/4.02  --inst_prop_sim_new                     false
% 27.43/4.02  --inst_subs_new                         false
% 27.43/4.02  --inst_eq_res_simp                      false
% 27.43/4.02  --inst_subs_given                       false
% 27.43/4.02  --inst_orphan_elimination               true
% 27.43/4.02  --inst_learning_loop_flag               true
% 27.43/4.02  --inst_learning_start                   3000
% 27.43/4.02  --inst_learning_factor                  2
% 27.43/4.02  --inst_start_prop_sim_after_learn       3
% 27.43/4.02  --inst_sel_renew                        solver
% 27.43/4.02  --inst_lit_activity_flag                true
% 27.43/4.02  --inst_restr_to_given                   false
% 27.43/4.02  --inst_activity_threshold               500
% 27.43/4.02  --inst_out_proof                        true
% 27.43/4.02  
% 27.43/4.02  ------ Resolution Options
% 27.43/4.02  
% 27.43/4.02  --resolution_flag                       true
% 27.43/4.02  --res_lit_sel                           adaptive
% 27.43/4.02  --res_lit_sel_side                      none
% 27.43/4.02  --res_ordering                          kbo
% 27.43/4.02  --res_to_prop_solver                    active
% 27.43/4.02  --res_prop_simpl_new                    false
% 27.43/4.02  --res_prop_simpl_given                  true
% 27.43/4.02  --res_passive_queue_type                priority_queues
% 27.43/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.43/4.02  --res_passive_queues_freq               [15;5]
% 27.43/4.02  --res_forward_subs                      full
% 27.43/4.02  --res_backward_subs                     full
% 27.43/4.02  --res_forward_subs_resolution           true
% 27.43/4.02  --res_backward_subs_resolution          true
% 27.43/4.02  --res_orphan_elimination                true
% 27.43/4.02  --res_time_limit                        2.
% 27.43/4.02  --res_out_proof                         true
% 27.43/4.02  
% 27.43/4.02  ------ Superposition Options
% 27.43/4.02  
% 27.43/4.02  --superposition_flag                    true
% 27.43/4.02  --sup_passive_queue_type                priority_queues
% 27.43/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.43/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.43/4.02  --demod_completeness_check              fast
% 27.43/4.02  --demod_use_ground                      true
% 27.43/4.02  --sup_to_prop_solver                    passive
% 27.43/4.02  --sup_prop_simpl_new                    true
% 27.43/4.02  --sup_prop_simpl_given                  true
% 27.43/4.02  --sup_fun_splitting                     true
% 27.43/4.02  --sup_smt_interval                      50000
% 27.43/4.02  
% 27.43/4.02  ------ Superposition Simplification Setup
% 27.43/4.02  
% 27.43/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.43/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.43/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.43/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.43/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.43/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.43/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.43/4.02  --sup_immed_triv                        [TrivRules]
% 27.43/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/4.02  --sup_immed_bw_main                     []
% 27.43/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.43/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.43/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/4.02  --sup_input_bw                          []
% 27.43/4.02  
% 27.43/4.02  ------ Combination Options
% 27.43/4.02  
% 27.43/4.02  --comb_res_mult                         3
% 27.43/4.02  --comb_sup_mult                         2
% 27.43/4.02  --comb_inst_mult                        10
% 27.43/4.02  
% 27.43/4.02  ------ Debug Options
% 27.43/4.02  
% 27.43/4.02  --dbg_backtrace                         false
% 27.43/4.02  --dbg_dump_prop_clauses                 false
% 27.43/4.02  --dbg_dump_prop_clauses_file            -
% 27.43/4.02  --dbg_out_stat                          false
% 27.43/4.02  ------ Parsing...
% 27.43/4.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.43/4.02  
% 27.43/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.43/4.02  
% 27.43/4.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.43/4.02  
% 27.43/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.43/4.02  ------ Proving...
% 27.43/4.02  ------ Problem Properties 
% 27.43/4.02  
% 27.43/4.02  
% 27.43/4.02  clauses                                 33
% 27.43/4.02  conjectures                             14
% 27.43/4.02  EPR                                     12
% 27.43/4.02  Horn                                    23
% 27.43/4.02  unary                                   15
% 27.43/4.02  binary                                  5
% 27.43/4.02  lits                                    135
% 27.43/4.02  lits eq                                 17
% 27.43/4.02  fd_pure                                 0
% 27.43/4.02  fd_pseudo                               0
% 27.43/4.02  fd_cond                                 0
% 27.43/4.02  fd_pseudo_cond                          1
% 27.43/4.02  AC symbols                              0
% 27.43/4.02  
% 27.43/4.02  ------ Schedule dynamic 5 is on 
% 27.43/4.02  
% 27.43/4.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.43/4.02  
% 27.43/4.02  
% 27.43/4.02  ------ 
% 27.43/4.02  Current options:
% 27.43/4.02  ------ 
% 27.43/4.02  
% 27.43/4.02  ------ Input Options
% 27.43/4.02  
% 27.43/4.02  --out_options                           all
% 27.43/4.02  --tptp_safe_out                         true
% 27.43/4.02  --problem_path                          ""
% 27.43/4.02  --include_path                          ""
% 27.43/4.02  --clausifier                            res/vclausify_rel
% 27.43/4.02  --clausifier_options                    ""
% 27.43/4.02  --stdin                                 false
% 27.43/4.02  --stats_out                             all
% 27.43/4.02  
% 27.43/4.02  ------ General Options
% 27.43/4.02  
% 27.43/4.02  --fof                                   false
% 27.43/4.02  --time_out_real                         305.
% 27.43/4.02  --time_out_virtual                      -1.
% 27.43/4.02  --symbol_type_check                     false
% 27.43/4.02  --clausify_out                          false
% 27.43/4.02  --sig_cnt_out                           false
% 27.43/4.02  --trig_cnt_out                          false
% 27.43/4.02  --trig_cnt_out_tolerance                1.
% 27.43/4.02  --trig_cnt_out_sk_spl                   false
% 27.43/4.02  --abstr_cl_out                          false
% 27.43/4.02  
% 27.43/4.02  ------ Global Options
% 27.43/4.02  
% 27.43/4.02  --schedule                              default
% 27.43/4.02  --add_important_lit                     false
% 27.43/4.02  --prop_solver_per_cl                    1000
% 27.43/4.02  --min_unsat_core                        false
% 27.43/4.02  --soft_assumptions                      false
% 27.43/4.02  --soft_lemma_size                       3
% 27.43/4.02  --prop_impl_unit_size                   0
% 27.43/4.02  --prop_impl_unit                        []
% 27.43/4.02  --share_sel_clauses                     true
% 27.43/4.02  --reset_solvers                         false
% 27.43/4.02  --bc_imp_inh                            [conj_cone]
% 27.43/4.02  --conj_cone_tolerance                   3.
% 27.43/4.02  --extra_neg_conj                        none
% 27.43/4.02  --large_theory_mode                     true
% 27.43/4.02  --prolific_symb_bound                   200
% 27.43/4.02  --lt_threshold                          2000
% 27.43/4.02  --clause_weak_htbl                      true
% 27.43/4.02  --gc_record_bc_elim                     false
% 27.43/4.02  
% 27.43/4.02  ------ Preprocessing Options
% 27.43/4.02  
% 27.43/4.02  --preprocessing_flag                    true
% 27.43/4.02  --time_out_prep_mult                    0.1
% 27.43/4.02  --splitting_mode                        input
% 27.43/4.02  --splitting_grd                         true
% 27.43/4.02  --splitting_cvd                         false
% 27.43/4.02  --splitting_cvd_svl                     false
% 27.43/4.02  --splitting_nvd                         32
% 27.43/4.02  --sub_typing                            true
% 27.43/4.02  --prep_gs_sim                           true
% 27.43/4.02  --prep_unflatten                        true
% 27.43/4.02  --prep_res_sim                          true
% 27.43/4.02  --prep_upred                            true
% 27.43/4.02  --prep_sem_filter                       exhaustive
% 27.43/4.02  --prep_sem_filter_out                   false
% 27.43/4.02  --pred_elim                             true
% 27.43/4.02  --res_sim_input                         true
% 27.43/4.02  --eq_ax_congr_red                       true
% 27.43/4.02  --pure_diseq_elim                       true
% 27.43/4.02  --brand_transform                       false
% 27.43/4.02  --non_eq_to_eq                          false
% 27.43/4.02  --prep_def_merge                        true
% 27.43/4.02  --prep_def_merge_prop_impl              false
% 27.43/4.02  --prep_def_merge_mbd                    true
% 27.43/4.02  --prep_def_merge_tr_red                 false
% 27.43/4.02  --prep_def_merge_tr_cl                  false
% 27.43/4.02  --smt_preprocessing                     true
% 27.43/4.02  --smt_ac_axioms                         fast
% 27.43/4.02  --preprocessed_out                      false
% 27.43/4.02  --preprocessed_stats                    false
% 27.43/4.02  
% 27.43/4.02  ------ Abstraction refinement Options
% 27.43/4.02  
% 27.43/4.02  --abstr_ref                             []
% 27.43/4.02  --abstr_ref_prep                        false
% 27.43/4.02  --abstr_ref_until_sat                   false
% 27.43/4.02  --abstr_ref_sig_restrict                funpre
% 27.43/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.43/4.02  --abstr_ref_under                       []
% 27.43/4.02  
% 27.43/4.02  ------ SAT Options
% 27.43/4.02  
% 27.43/4.02  --sat_mode                              false
% 27.43/4.02  --sat_fm_restart_options                ""
% 27.43/4.02  --sat_gr_def                            false
% 27.43/4.02  --sat_epr_types                         true
% 27.43/4.02  --sat_non_cyclic_types                  false
% 27.43/4.02  --sat_finite_models                     false
% 27.43/4.02  --sat_fm_lemmas                         false
% 27.43/4.02  --sat_fm_prep                           false
% 27.43/4.02  --sat_fm_uc_incr                        true
% 27.43/4.02  --sat_out_model                         small
% 27.43/4.02  --sat_out_clauses                       false
% 27.43/4.02  
% 27.43/4.02  ------ QBF Options
% 27.43/4.02  
% 27.43/4.02  --qbf_mode                              false
% 27.43/4.02  --qbf_elim_univ                         false
% 27.43/4.02  --qbf_dom_inst                          none
% 27.43/4.02  --qbf_dom_pre_inst                      false
% 27.43/4.02  --qbf_sk_in                             false
% 27.43/4.02  --qbf_pred_elim                         true
% 27.43/4.02  --qbf_split                             512
% 27.43/4.02  
% 27.43/4.02  ------ BMC1 Options
% 27.43/4.02  
% 27.43/4.02  --bmc1_incremental                      false
% 27.43/4.02  --bmc1_axioms                           reachable_all
% 27.43/4.02  --bmc1_min_bound                        0
% 27.43/4.02  --bmc1_max_bound                        -1
% 27.43/4.02  --bmc1_max_bound_default                -1
% 27.43/4.02  --bmc1_symbol_reachability              true
% 27.43/4.02  --bmc1_property_lemmas                  false
% 27.43/4.02  --bmc1_k_induction                      false
% 27.43/4.02  --bmc1_non_equiv_states                 false
% 27.43/4.02  --bmc1_deadlock                         false
% 27.43/4.02  --bmc1_ucm                              false
% 27.43/4.02  --bmc1_add_unsat_core                   none
% 27.43/4.02  --bmc1_unsat_core_children              false
% 27.43/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.43/4.02  --bmc1_out_stat                         full
% 27.43/4.02  --bmc1_ground_init                      false
% 27.43/4.02  --bmc1_pre_inst_next_state              false
% 27.43/4.02  --bmc1_pre_inst_state                   false
% 27.43/4.02  --bmc1_pre_inst_reach_state             false
% 27.43/4.02  --bmc1_out_unsat_core                   false
% 27.43/4.02  --bmc1_aig_witness_out                  false
% 27.43/4.02  --bmc1_verbose                          false
% 27.43/4.02  --bmc1_dump_clauses_tptp                false
% 27.43/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.43/4.02  --bmc1_dump_file                        -
% 27.43/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.43/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.43/4.02  --bmc1_ucm_extend_mode                  1
% 27.43/4.02  --bmc1_ucm_init_mode                    2
% 27.43/4.02  --bmc1_ucm_cone_mode                    none
% 27.43/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.43/4.02  --bmc1_ucm_relax_model                  4
% 27.43/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.43/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.43/4.02  --bmc1_ucm_layered_model                none
% 27.43/4.02  --bmc1_ucm_max_lemma_size               10
% 27.43/4.02  
% 27.43/4.02  ------ AIG Options
% 27.43/4.02  
% 27.43/4.02  --aig_mode                              false
% 27.43/4.02  
% 27.43/4.02  ------ Instantiation Options
% 27.43/4.02  
% 27.43/4.02  --instantiation_flag                    true
% 27.43/4.02  --inst_sos_flag                         true
% 27.43/4.02  --inst_sos_phase                        true
% 27.43/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.43/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.43/4.02  --inst_lit_sel_side                     none
% 27.43/4.02  --inst_solver_per_active                1400
% 27.43/4.02  --inst_solver_calls_frac                1.
% 27.43/4.02  --inst_passive_queue_type               priority_queues
% 27.43/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.43/4.02  --inst_passive_queues_freq              [25;2]
% 27.43/4.02  --inst_dismatching                      true
% 27.43/4.02  --inst_eager_unprocessed_to_passive     true
% 27.43/4.02  --inst_prop_sim_given                   true
% 27.43/4.02  --inst_prop_sim_new                     false
% 27.43/4.02  --inst_subs_new                         false
% 27.43/4.02  --inst_eq_res_simp                      false
% 27.43/4.02  --inst_subs_given                       false
% 27.43/4.02  --inst_orphan_elimination               true
% 27.43/4.02  --inst_learning_loop_flag               true
% 27.43/4.02  --inst_learning_start                   3000
% 27.43/4.02  --inst_learning_factor                  2
% 27.43/4.02  --inst_start_prop_sim_after_learn       3
% 27.43/4.02  --inst_sel_renew                        solver
% 27.43/4.02  --inst_lit_activity_flag                true
% 27.43/4.02  --inst_restr_to_given                   false
% 27.43/4.02  --inst_activity_threshold               500
% 27.43/4.02  --inst_out_proof                        true
% 27.43/4.02  
% 27.43/4.02  ------ Resolution Options
% 27.43/4.02  
% 27.43/4.02  --resolution_flag                       false
% 27.43/4.02  --res_lit_sel                           adaptive
% 27.43/4.02  --res_lit_sel_side                      none
% 27.43/4.02  --res_ordering                          kbo
% 27.43/4.02  --res_to_prop_solver                    active
% 27.43/4.02  --res_prop_simpl_new                    false
% 27.43/4.02  --res_prop_simpl_given                  true
% 27.43/4.02  --res_passive_queue_type                priority_queues
% 27.43/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.43/4.02  --res_passive_queues_freq               [15;5]
% 27.43/4.02  --res_forward_subs                      full
% 27.43/4.02  --res_backward_subs                     full
% 27.43/4.02  --res_forward_subs_resolution           true
% 27.43/4.02  --res_backward_subs_resolution          true
% 27.43/4.02  --res_orphan_elimination                true
% 27.43/4.02  --res_time_limit                        2.
% 27.43/4.02  --res_out_proof                         true
% 27.43/4.02  
% 27.43/4.02  ------ Superposition Options
% 27.43/4.02  
% 27.43/4.02  --superposition_flag                    true
% 27.43/4.02  --sup_passive_queue_type                priority_queues
% 27.43/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.43/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.43/4.02  --demod_completeness_check              fast
% 27.43/4.02  --demod_use_ground                      true
% 27.43/4.02  --sup_to_prop_solver                    passive
% 27.43/4.02  --sup_prop_simpl_new                    true
% 27.43/4.02  --sup_prop_simpl_given                  true
% 27.43/4.02  --sup_fun_splitting                     true
% 27.43/4.02  --sup_smt_interval                      50000
% 27.43/4.02  
% 27.43/4.02  ------ Superposition Simplification Setup
% 27.43/4.02  
% 27.43/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.43/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.43/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.43/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.43/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.43/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.43/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.43/4.02  --sup_immed_triv                        [TrivRules]
% 27.43/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/4.02  --sup_immed_bw_main                     []
% 27.43/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.43/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.43/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.43/4.02  --sup_input_bw                          []
% 27.43/4.02  
% 27.43/4.02  ------ Combination Options
% 27.43/4.02  
% 27.43/4.02  --comb_res_mult                         3
% 27.43/4.02  --comb_sup_mult                         2
% 27.43/4.02  --comb_inst_mult                        10
% 27.43/4.02  
% 27.43/4.02  ------ Debug Options
% 27.43/4.02  
% 27.43/4.02  --dbg_backtrace                         false
% 27.43/4.02  --dbg_dump_prop_clauses                 false
% 27.43/4.02  --dbg_dump_prop_clauses_file            -
% 27.43/4.02  --dbg_out_stat                          false
% 27.43/4.02  
% 27.43/4.02  
% 27.43/4.02  
% 27.43/4.02  
% 27.43/4.02  ------ Proving...
% 27.43/4.02  
% 27.43/4.02  
% 27.43/4.02  % SZS status Theorem for theBenchmark.p
% 27.43/4.02  
% 27.43/4.02   Resolution empty clause
% 27.43/4.02  
% 27.43/4.02  % SZS output start CNFRefutation for theBenchmark.p
% 27.43/4.02  
% 27.43/4.02  fof(f17,conjecture,(
% 27.43/4.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f18,negated_conjecture,(
% 27.43/4.02    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 27.43/4.02    inference(negated_conjecture,[],[f17])).
% 27.43/4.02  
% 27.43/4.02  fof(f40,plain,(
% 27.43/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 27.43/4.02    inference(ennf_transformation,[],[f18])).
% 27.43/4.02  
% 27.43/4.02  fof(f41,plain,(
% 27.43/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 27.43/4.02    inference(flattening,[],[f40])).
% 27.43/4.02  
% 27.43/4.02  fof(f52,plain,(
% 27.43/4.02    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 27.43/4.02    introduced(choice_axiom,[])).
% 27.43/4.02  
% 27.43/4.02  fof(f51,plain,(
% 27.43/4.02    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 27.43/4.02    introduced(choice_axiom,[])).
% 27.43/4.02  
% 27.43/4.02  fof(f50,plain,(
% 27.43/4.02    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 27.43/4.02    introduced(choice_axiom,[])).
% 27.43/4.02  
% 27.43/4.02  fof(f49,plain,(
% 27.43/4.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 27.43/4.02    introduced(choice_axiom,[])).
% 27.43/4.02  
% 27.43/4.02  fof(f48,plain,(
% 27.43/4.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 27.43/4.02    introduced(choice_axiom,[])).
% 27.43/4.02  
% 27.43/4.02  fof(f47,plain,(
% 27.43/4.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 27.43/4.02    introduced(choice_axiom,[])).
% 27.43/4.02  
% 27.43/4.02  fof(f53,plain,(
% 27.43/4.02    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 27.43/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f41,f52,f51,f50,f49,f48,f47])).
% 27.43/4.02  
% 27.43/4.02  fof(f83,plain,(
% 27.43/4.02    r1_subset_1(sK2,sK3)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f9,axiom,(
% 27.43/4.02    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f26,plain,(
% 27.43/4.02    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 27.43/4.02    inference(ennf_transformation,[],[f9])).
% 27.43/4.02  
% 27.43/4.02  fof(f27,plain,(
% 27.43/4.02    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 27.43/4.02    inference(flattening,[],[f26])).
% 27.43/4.02  
% 27.43/4.02  fof(f63,plain,(
% 27.43/4.02    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f27])).
% 27.43/4.02  
% 27.43/4.02  fof(f79,plain,(
% 27.43/4.02    ~v1_xboole_0(sK2)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f81,plain,(
% 27.43/4.02    ~v1_xboole_0(sK3)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f8,axiom,(
% 27.43/4.02    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f24,plain,(
% 27.43/4.02    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 27.43/4.02    inference(ennf_transformation,[],[f8])).
% 27.43/4.02  
% 27.43/4.02  fof(f25,plain,(
% 27.43/4.02    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 27.43/4.02    inference(flattening,[],[f24])).
% 27.43/4.02  
% 27.43/4.02  fof(f43,plain,(
% 27.43/4.02    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 27.43/4.02    inference(nnf_transformation,[],[f25])).
% 27.43/4.02  
% 27.43/4.02  fof(f61,plain,(
% 27.43/4.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f43])).
% 27.43/4.02  
% 27.43/4.02  fof(f1,axiom,(
% 27.43/4.02    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f42,plain,(
% 27.43/4.02    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 27.43/4.02    inference(nnf_transformation,[],[f1])).
% 27.43/4.02  
% 27.43/4.02  fof(f54,plain,(
% 27.43/4.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f42])).
% 27.43/4.02  
% 27.43/4.02  fof(f89,plain,(
% 27.43/4.02    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f12,axiom,(
% 27.43/4.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f30,plain,(
% 27.43/4.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 27.43/4.02    inference(ennf_transformation,[],[f12])).
% 27.43/4.02  
% 27.43/4.02  fof(f31,plain,(
% 27.43/4.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 27.43/4.02    inference(flattening,[],[f30])).
% 27.43/4.02  
% 27.43/4.02  fof(f67,plain,(
% 27.43/4.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f31])).
% 27.43/4.02  
% 27.43/4.02  fof(f11,axiom,(
% 27.43/4.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f19,plain,(
% 27.43/4.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 27.43/4.02    inference(pure_predicate_removal,[],[f11])).
% 27.43/4.02  
% 27.43/4.02  fof(f29,plain,(
% 27.43/4.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.43/4.02    inference(ennf_transformation,[],[f19])).
% 27.43/4.02  
% 27.43/4.02  fof(f65,plain,(
% 27.43/4.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.43/4.02    inference(cnf_transformation,[],[f29])).
% 27.43/4.02  
% 27.43/4.02  fof(f13,axiom,(
% 27.43/4.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f32,plain,(
% 27.43/4.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.43/4.02    inference(ennf_transformation,[],[f13])).
% 27.43/4.02  
% 27.43/4.02  fof(f33,plain,(
% 27.43/4.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.43/4.02    inference(flattening,[],[f32])).
% 27.43/4.02  
% 27.43/4.02  fof(f44,plain,(
% 27.43/4.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.43/4.02    inference(nnf_transformation,[],[f33])).
% 27.43/4.02  
% 27.43/4.02  fof(f68,plain,(
% 27.43/4.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f44])).
% 27.43/4.02  
% 27.43/4.02  fof(f10,axiom,(
% 27.43/4.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f28,plain,(
% 27.43/4.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.43/4.02    inference(ennf_transformation,[],[f10])).
% 27.43/4.02  
% 27.43/4.02  fof(f64,plain,(
% 27.43/4.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.43/4.02    inference(cnf_transformation,[],[f28])).
% 27.43/4.02  
% 27.43/4.02  fof(f78,plain,(
% 27.43/4.02    ~v1_xboole_0(sK1)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f87,plain,(
% 27.43/4.02    v1_funct_1(sK5)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f88,plain,(
% 27.43/4.02    v1_funct_2(sK5,sK3,sK1)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f7,axiom,(
% 27.43/4.02    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f23,plain,(
% 27.43/4.02    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 27.43/4.02    inference(ennf_transformation,[],[f7])).
% 27.43/4.02  
% 27.43/4.02  fof(f60,plain,(
% 27.43/4.02    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f23])).
% 27.43/4.02  
% 27.43/4.02  fof(f6,axiom,(
% 27.43/4.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f22,plain,(
% 27.43/4.02    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 27.43/4.02    inference(ennf_transformation,[],[f6])).
% 27.43/4.02  
% 27.43/4.02  fof(f59,plain,(
% 27.43/4.02    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f22])).
% 27.43/4.02  
% 27.43/4.02  fof(f2,axiom,(
% 27.43/4.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f56,plain,(
% 27.43/4.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 27.43/4.02    inference(cnf_transformation,[],[f2])).
% 27.43/4.02  
% 27.43/4.02  fof(f55,plain,(
% 27.43/4.02    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.43/4.02    inference(cnf_transformation,[],[f42])).
% 27.43/4.02  
% 27.43/4.02  fof(f4,axiom,(
% 27.43/4.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f58,plain,(
% 27.43/4.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 27.43/4.02    inference(cnf_transformation,[],[f4])).
% 27.43/4.02  
% 27.43/4.02  fof(f86,plain,(
% 27.43/4.02    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f84,plain,(
% 27.43/4.02    v1_funct_1(sK4)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f85,plain,(
% 27.43/4.02    v1_funct_2(sK4,sK2,sK1)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f82,plain,(
% 27.43/4.02    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f16,axiom,(
% 27.43/4.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f38,plain,(
% 27.43/4.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 27.43/4.02    inference(ennf_transformation,[],[f16])).
% 27.43/4.02  
% 27.43/4.02  fof(f39,plain,(
% 27.43/4.02    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 27.43/4.02    inference(flattening,[],[f38])).
% 27.43/4.02  
% 27.43/4.02  fof(f74,plain,(
% 27.43/4.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f39])).
% 27.43/4.02  
% 27.43/4.02  fof(f76,plain,(
% 27.43/4.02    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f39])).
% 27.43/4.02  
% 27.43/4.02  fof(f14,axiom,(
% 27.43/4.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f34,plain,(
% 27.43/4.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 27.43/4.02    inference(ennf_transformation,[],[f14])).
% 27.43/4.02  
% 27.43/4.02  fof(f35,plain,(
% 27.43/4.02    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 27.43/4.02    inference(flattening,[],[f34])).
% 27.43/4.02  
% 27.43/4.02  fof(f70,plain,(
% 27.43/4.02    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 27.43/4.02    inference(cnf_transformation,[],[f35])).
% 27.43/4.02  
% 27.43/4.02  fof(f77,plain,(
% 27.43/4.02    ~v1_xboole_0(sK0)),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f80,plain,(
% 27.43/4.02    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 27.43/4.02    inference(cnf_transformation,[],[f53])).
% 27.43/4.02  
% 27.43/4.02  fof(f3,axiom,(
% 27.43/4.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 27.43/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.43/4.02  
% 27.43/4.02  fof(f21,plain,(
% 27.43/4.02    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 27.43/4.02    inference(ennf_transformation,[],[f3])).
% 27.43/4.02  
% 27.43/4.02  fof(f57,plain,(
% 27.43/4.02    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 27.43/4.02    inference(cnf_transformation,[],[f21])).
% 27.43/4.02  
% 27.43/4.02  fof(f90,plain,(
% 27.43/4.02    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 27.58/4.02    inference(cnf_transformation,[],[f53])).
% 27.58/4.02  
% 27.58/4.02  fof(f15,axiom,(
% 27.58/4.02    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 27.58/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.58/4.02  
% 27.58/4.02  fof(f36,plain,(
% 27.58/4.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 27.58/4.02    inference(ennf_transformation,[],[f15])).
% 27.58/4.02  
% 27.58/4.02  fof(f37,plain,(
% 27.58/4.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 27.58/4.02    inference(flattening,[],[f36])).
% 27.58/4.02  
% 27.58/4.02  fof(f45,plain,(
% 27.58/4.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 27.58/4.02    inference(nnf_transformation,[],[f37])).
% 27.58/4.02  
% 27.58/4.02  fof(f46,plain,(
% 27.58/4.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 27.58/4.02    inference(flattening,[],[f45])).
% 27.58/4.02  
% 27.58/4.02  fof(f71,plain,(
% 27.58/4.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.58/4.02    inference(cnf_transformation,[],[f46])).
% 27.58/4.02  
% 27.58/4.02  fof(f95,plain,(
% 27.58/4.02    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.58/4.02    inference(equality_resolution,[],[f71])).
% 27.58/4.02  
% 27.58/4.02  fof(f75,plain,(
% 27.58/4.02    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.58/4.02    inference(cnf_transformation,[],[f39])).
% 27.58/4.02  
% 27.58/4.02  fof(f72,plain,(
% 27.58/4.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.58/4.02    inference(cnf_transformation,[],[f46])).
% 27.58/4.02  
% 27.58/4.02  fof(f94,plain,(
% 27.58/4.02    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 27.58/4.02    inference(equality_resolution,[],[f72])).
% 27.58/4.02  
% 27.58/4.02  cnf(c_30,negated_conjecture,
% 27.58/4.02      ( r1_subset_1(sK2,sK3) ),
% 27.58/4.02      inference(cnf_transformation,[],[f83]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1057,negated_conjecture,
% 27.58/4.02      ( r1_subset_1(sK2,sK3) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_30]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1865,plain,
% 27.58/4.02      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_9,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0,X1)
% 27.58/4.02      | r1_subset_1(X1,X0)
% 27.58/4.02      | v1_xboole_0(X0)
% 27.58/4.02      | v1_xboole_0(X1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f63]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1071,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0_53,X1_53)
% 27.58/4.02      | r1_subset_1(X1_53,X0_53)
% 27.58/4.02      | v1_xboole_0(X1_53)
% 27.58/4.02      | v1_xboole_0(X0_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_9]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1852,plain,
% 27.58/4.02      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 27.58/4.02      | r1_subset_1(X1_53,X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1071]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3591,plain,
% 27.58/4.02      ( r1_subset_1(sK3,sK2) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1865,c_1852]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_34,negated_conjecture,
% 27.58/4.02      ( ~ v1_xboole_0(sK2) ),
% 27.58/4.02      inference(cnf_transformation,[],[f79]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_39,plain,
% 27.58/4.02      ( v1_xboole_0(sK2) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_32,negated_conjecture,
% 27.58/4.02      ( ~ v1_xboole_0(sK3) ),
% 27.58/4.02      inference(cnf_transformation,[],[f81]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_41,plain,
% 27.58/4.02      ( v1_xboole_0(sK3) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_43,plain,
% 27.58/4.02      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2109,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0_53,sK3)
% 27.58/4.02      | r1_subset_1(sK3,X0_53)
% 27.58/4.02      | v1_xboole_0(X0_53)
% 27.58/4.02      | v1_xboole_0(sK3) ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1071]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2121,plain,
% 27.58/4.02      ( r1_subset_1(X0_53,sK3) != iProver_top
% 27.58/4.02      | r1_subset_1(sK3,X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2123,plain,
% 27.58/4.02      ( r1_subset_1(sK3,sK2) = iProver_top
% 27.58/4.02      | r1_subset_1(sK2,sK3) != iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_2121]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3611,plain,
% 27.58/4.02      ( r1_subset_1(sK3,sK2) = iProver_top ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_3591,c_39,c_41,c_43,c_2123]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_8,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0,X1)
% 27.58/4.02      | r1_xboole_0(X0,X1)
% 27.58/4.02      | v1_xboole_0(X0)
% 27.58/4.02      | v1_xboole_0(X1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f61]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1072,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0_53,X1_53)
% 27.58/4.02      | r1_xboole_0(X0_53,X1_53)
% 27.58/4.02      | v1_xboole_0(X1_53)
% 27.58/4.02      | v1_xboole_0(X0_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_8]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1851,plain,
% 27.58/4.02      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 27.58/4.02      | r1_xboole_0(X0_53,X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1072]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3616,plain,
% 27.58/4.02      ( r1_xboole_0(sK3,sK2) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3611,c_1851]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2065,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0_53,sK2)
% 27.58/4.02      | r1_xboole_0(X0_53,sK2)
% 27.58/4.02      | v1_xboole_0(X0_53)
% 27.58/4.02      | v1_xboole_0(sK2) ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1072]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2256,plain,
% 27.58/4.02      ( ~ r1_subset_1(sK3,sK2)
% 27.58/4.02      | r1_xboole_0(sK3,sK2)
% 27.58/4.02      | v1_xboole_0(sK3)
% 27.58/4.02      | v1_xboole_0(sK2) ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_2065]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2260,plain,
% 27.58/4.02      ( r1_subset_1(sK3,sK2) != iProver_top
% 27.58/4.02      | r1_xboole_0(sK3,sK2) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_2256]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3674,plain,
% 27.58/4.02      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_3616,c_39,c_41,c_43,c_2123,c_2260]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1,plain,
% 27.58/4.02      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.58/4.02      inference(cnf_transformation,[],[f54]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1079,plain,
% 27.58/4.02      ( ~ r1_xboole_0(X0_53,X1_53) | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_1]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1845,plain,
% 27.58/4.02      ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,X1_53) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1079]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3678,plain,
% 27.58/4.02      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3674,c_1845]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_24,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 27.58/4.02      inference(cnf_transformation,[],[f89]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1063,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_24]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1859,plain,
% 27.58/4.02      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1063]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_12,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.02      | v1_partfun1(X0,X1)
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | v1_xboole_0(X2) ),
% 27.58/4.02      inference(cnf_transformation,[],[f67]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_11,plain,
% 27.58/4.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.58/4.02      inference(cnf_transformation,[],[f65]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15,plain,
% 27.58/4.02      ( ~ v1_partfun1(X0,X1)
% 27.58/4.02      | ~ v4_relat_1(X0,X1)
% 27.58/4.02      | ~ v1_relat_1(X0)
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(cnf_transformation,[],[f68]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_465,plain,
% 27.58/4.02      ( ~ v1_partfun1(X0,X1)
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ v1_relat_1(X0)
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(resolution,[status(thm)],[c_11,c_15]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_10,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 27.58/4.02      inference(cnf_transformation,[],[f64]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_469,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ v1_partfun1(X0,X1)
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_465,c_15,c_11,c_10]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_470,plain,
% 27.58/4.02      ( ~ v1_partfun1(X0,X1)
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(renaming,[status(thm)],[c_469]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_540,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | v1_xboole_0(X2)
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(resolution,[status(thm)],[c_12,c_470]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_544,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ v1_funct_2(X0,X1,X2)
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | v1_xboole_0(X2)
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_540,c_15,c_12,c_11,c_10]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_545,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | v1_xboole_0(X2)
% 27.58/4.02      | k1_relat_1(X0) = X1 ),
% 27.58/4.02      inference(renaming,[status(thm)],[c_544]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1048,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 27.58/4.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.02      | ~ v1_funct_1(X0_53)
% 27.58/4.02      | v1_xboole_0(X2_53)
% 27.58/4.02      | k1_relat_1(X0_53) = X1_53 ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_545]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1874,plain,
% 27.58/4.02      ( k1_relat_1(X0_53) = X1_53
% 27.58/4.02      | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 27.58/4.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 27.58/4.02      | v1_funct_1(X0_53) != iProver_top
% 27.58/4.02      | v1_xboole_0(X2_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1048]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_6844,plain,
% 27.58/4.02      ( k1_relat_1(sK5) = sK3
% 27.58/4.02      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 27.58/4.02      | v1_funct_1(sK5) != iProver_top
% 27.58/4.02      | v1_xboole_0(sK1) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1859,c_1874]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_35,negated_conjecture,
% 27.58/4.02      ( ~ v1_xboole_0(sK1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f78]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_26,negated_conjecture,
% 27.58/4.02      ( v1_funct_1(sK5) ),
% 27.58/4.02      inference(cnf_transformation,[],[f87]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_25,negated_conjecture,
% 27.58/4.02      ( v1_funct_2(sK5,sK3,sK1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f88]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1976,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0_53,X1_53,sK1)
% 27.58/4.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1)))
% 27.58/4.02      | ~ v1_funct_1(X0_53)
% 27.58/4.02      | v1_xboole_0(sK1)
% 27.58/4.02      | k1_relat_1(X0_53) = X1_53 ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1048]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2275,plain,
% 27.58/4.02      ( ~ v1_funct_2(sK5,X0_53,sK1)
% 27.58/4.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
% 27.58/4.02      | ~ v1_funct_1(sK5)
% 27.58/4.02      | v1_xboole_0(sK1)
% 27.58/4.02      | k1_relat_1(sK5) = X0_53 ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1976]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2650,plain,
% 27.58/4.02      ( ~ v1_funct_2(sK5,sK3,sK1)
% 27.58/4.02      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 27.58/4.02      | ~ v1_funct_1(sK5)
% 27.58/4.02      | v1_xboole_0(sK1)
% 27.58/4.02      | k1_relat_1(sK5) = sK3 ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_2275]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_6987,plain,
% 27.58/4.02      ( k1_relat_1(sK5) = sK3 ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_6844,c_35,c_26,c_25,c_24,c_2650]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1070,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.02      | v1_relat_1(X0_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_10]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1853,plain,
% 27.58/4.02      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 27.58/4.02      | v1_relat_1(X0_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1070]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3216,plain,
% 27.58/4.02      ( v1_relat_1(sK5) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1859,c_1853]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_6,plain,
% 27.58/4.02      ( ~ v1_relat_1(X0)
% 27.58/4.02      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f60]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1074,plain,
% 27.58/4.02      ( ~ v1_relat_1(X0_53)
% 27.58/4.02      | k1_relat_1(k7_relat_1(X0_53,X1_53)) = k3_xboole_0(k1_relat_1(X0_53),X1_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_6]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1849,plain,
% 27.58/4.02      ( k1_relat_1(k7_relat_1(X0_53,X1_53)) = k3_xboole_0(k1_relat_1(X0_53),X1_53)
% 27.58/4.02      | v1_relat_1(X0_53) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1074]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3352,plain,
% 27.58/4.02      ( k1_relat_1(k7_relat_1(sK5,X0_53)) = k3_xboole_0(k1_relat_1(sK5),X0_53) ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3216,c_1849]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_6990,plain,
% 27.58/4.02      ( k1_relat_1(k7_relat_1(sK5,X0_53)) = k3_xboole_0(sK3,X0_53) ),
% 27.58/4.02      inference(demodulation,[status(thm)],[c_6987,c_3352]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_5,plain,
% 27.58/4.02      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 27.58/4.02      | ~ v1_relat_1(X1)
% 27.58/4.02      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 27.58/4.02      inference(cnf_transformation,[],[f59]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1075,plain,
% 27.58/4.02      ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
% 27.58/4.02      | ~ v1_relat_1(X1_53)
% 27.58/4.02      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_5]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1848,plain,
% 27.58/4.02      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
% 27.58/4.02      | v1_relat_1(X0_53) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7089,plain,
% 27.58/4.02      ( k7_relat_1(k7_relat_1(sK5,X0_53),X1_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X1_53,k3_xboole_0(sK3,X0_53)) != iProver_top
% 27.58/4.02      | v1_relat_1(k7_relat_1(sK5,X0_53)) != iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_6990,c_1848]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7384,plain,
% 27.58/4.02      ( k7_relat_1(k7_relat_1(sK5,sK2),X0_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,k1_xboole_0) != iProver_top
% 27.58/4.02      | v1_relat_1(k7_relat_1(sK5,sK2)) != iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3678,c_7089]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3477,plain,
% 27.58/4.02      ( r1_xboole_0(sK2,sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1865,c_1851]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2110,plain,
% 27.58/4.02      ( ~ r1_subset_1(X0_53,sK3)
% 27.58/4.02      | r1_xboole_0(X0_53,sK3)
% 27.58/4.02      | v1_xboole_0(X0_53)
% 27.58/4.02      | v1_xboole_0(sK3) ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1072]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2117,plain,
% 27.58/4.02      ( r1_subset_1(X0_53,sK3) != iProver_top
% 27.58/4.02      | r1_xboole_0(X0_53,sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_2110]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2119,plain,
% 27.58/4.02      ( r1_subset_1(sK2,sK3) != iProver_top
% 27.58/4.02      | r1_xboole_0(sK2,sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_2117]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3594,plain,
% 27.58/4.02      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_3477,c_39,c_41,c_43,c_2119]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_6994,plain,
% 27.58/4.02      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,sK3) != iProver_top
% 27.58/4.02      | v1_relat_1(sK5) != iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_6987,c_1848]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7140,plain,
% 27.58/4.02      ( r1_xboole_0(X0_53,sK3) != iProver_top
% 27.58/4.02      | k7_relat_1(sK5,X0_53) = k1_xboole_0 ),
% 27.58/4.02      inference(global_propositional_subsumption,[status(thm)],[c_6994,c_3216]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7141,plain,
% 27.58/4.02      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,sK3) != iProver_top ),
% 27.58/4.02      inference(renaming,[status(thm)],[c_7140]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7146,plain,
% 27.58/4.02      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3594,c_7141]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7385,plain,
% 27.58/4.02      ( k7_relat_1(k1_xboole_0,X0_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,k1_xboole_0) != iProver_top
% 27.58/4.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 27.58/4.02      inference(light_normalisation,[status(thm)],[c_7384,c_7146]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2,plain,
% 27.58/4.02      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 27.58/4.02      inference(cnf_transformation,[],[f56]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1078,plain,
% 27.58/4.02      ( k3_xboole_0(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_2]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_0,plain,
% 27.58/4.02      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 27.58/4.02      inference(cnf_transformation,[],[f55]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1080,plain,
% 27.58/4.02      ( r1_xboole_0(X0_53,X1_53) | k3_xboole_0(X0_53,X1_53) != k1_xboole_0 ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_0]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3030,plain,
% 27.58/4.02      ( r1_xboole_0(X0_53,k1_xboole_0)
% 27.58/4.02      | k3_xboole_0(X0_53,k1_xboole_0) != k1_xboole_0 ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1080]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3031,plain,
% 27.58/4.02      ( k3_xboole_0(X0_53,k1_xboole_0) != k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_3030]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_4,plain,
% 27.58/4.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 27.58/4.02      inference(cnf_transformation,[],[f58]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1076,plain,
% 27.58/4.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_53)) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_4]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1847,plain,
% 27.58/4.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_53)) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1076]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3218,plain,
% 27.58/4.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1847,c_1853]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_46088,plain,
% 27.58/4.02      ( k7_relat_1(k1_xboole_0,X0_53) = k1_xboole_0 ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_7385,c_1078,c_3031,c_3218]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7215,plain,
% 27.58/4.02      ( k3_xboole_0(sK3,sK2) = k1_relat_1(k1_xboole_0) ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_7146,c_6990]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7216,plain,
% 27.58/4.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 27.58/4.02      inference(light_normalisation,[status(thm)],[c_7215,c_3678]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3354,plain,
% 27.58/4.02      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0_53)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0_53) ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3218,c_1849]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_37541,plain,
% 27.58/4.02      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0_53)) = k3_xboole_0(k1_xboole_0,X0_53) ),
% 27.58/4.02      inference(demodulation,[status(thm)],[c_7216,c_3354]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_46093,plain,
% 27.58/4.02      ( k3_xboole_0(k1_xboole_0,X0_53) = k1_relat_1(k1_xboole_0) ),
% 27.58/4.02      inference(demodulation,[status(thm)],[c_46088,c_37541]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_46098,plain,
% 27.58/4.02      ( k3_xboole_0(k1_xboole_0,X0_53) = k1_xboole_0 ),
% 27.58/4.02      inference(light_normalisation,[status(thm)],[c_46093,c_7216]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1844,plain,
% 27.58/4.02      ( k3_xboole_0(X0_53,X1_53) != k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,X1_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1080]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_46438,plain,
% 27.58/4.02      ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_46098,c_1844]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_27,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 27.58/4.02      inference(cnf_transformation,[],[f86]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1060,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_27]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1862,plain,
% 27.58/4.02      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_6845,plain,
% 27.58/4.02      ( k1_relat_1(sK4) = sK2
% 27.58/4.02      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 27.58/4.02      | v1_funct_1(sK4) != iProver_top
% 27.58/4.02      | v1_xboole_0(sK1) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1862,c_1874]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_29,negated_conjecture,
% 27.58/4.02      ( v1_funct_1(sK4) ),
% 27.58/4.02      inference(cnf_transformation,[],[f84]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_28,negated_conjecture,
% 27.58/4.02      ( v1_funct_2(sK4,sK2,sK1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f85]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2280,plain,
% 27.58/4.02      ( ~ v1_funct_2(sK4,X0_53,sK1)
% 27.58/4.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1)))
% 27.58/4.02      | ~ v1_funct_1(sK4)
% 27.58/4.02      | v1_xboole_0(sK1)
% 27.58/4.02      | k1_relat_1(sK4) = X0_53 ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_1976]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2282,plain,
% 27.58/4.02      ( ~ v1_funct_2(sK4,sK2,sK1)
% 27.58/4.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 27.58/4.02      | ~ v1_funct_1(sK4)
% 27.58/4.02      | v1_xboole_0(sK1)
% 27.58/4.02      | k1_relat_1(sK4) = sK2 ),
% 27.58/4.02      inference(instantiation,[status(thm)],[c_2280]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7075,plain,
% 27.58/4.02      ( k1_relat_1(sK4) = sK2 ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_6845,c_35,c_29,c_28,c_27,c_2282]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7082,plain,
% 27.58/4.02      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,sK2) != iProver_top
% 27.58/4.02      | v1_relat_1(sK4) != iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_7075,c_1848]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3217,plain,
% 27.58/4.02      ( v1_relat_1(sK4) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1862,c_1853]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7218,plain,
% 27.58/4.02      ( r1_xboole_0(X0_53,sK2) != iProver_top
% 27.58/4.02      | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
% 27.58/4.02      inference(global_propositional_subsumption,[status(thm)],[c_7082,c_3217]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_7219,plain,
% 27.58/4.02      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 27.58/4.02      | r1_xboole_0(X0_53,sK2) != iProver_top ),
% 27.58/4.02      inference(renaming,[status(thm)],[c_7218]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_46649,plain,
% 27.58/4.02      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_46438,c_7219]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_31,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 27.58/4.02      inference(cnf_transformation,[],[f82]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1056,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_31]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1866,plain,
% 27.58/4.02      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1056]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_22,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.02      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | ~ v1_funct_1(X3)
% 27.58/4.02      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 27.58/4.02      | v1_xboole_0(X5)
% 27.58/4.02      | v1_xboole_0(X2)
% 27.58/4.02      | v1_xboole_0(X4)
% 27.58/4.02      | v1_xboole_0(X1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f74]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1065,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 27.58/4.02      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 27.58/4.02      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 27.58/4.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 27.58/4.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.02      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 27.58/4.02      | ~ v1_funct_1(X0_53)
% 27.58/4.02      | ~ v1_funct_1(X3_53)
% 27.58/4.02      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 27.58/4.02      | v1_xboole_0(X2_53)
% 27.58/4.02      | v1_xboole_0(X1_53)
% 27.58/4.02      | v1_xboole_0(X4_53)
% 27.58/4.02      | v1_xboole_0(X5_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_22]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1858,plain,
% 27.58/4.02      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 27.58/4.02      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 27.58/4.02      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 27.58/4.02      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 27.58/4.02      | v1_funct_1(X0_53) != iProver_top
% 27.58/4.02      | v1_funct_1(X3_53) != iProver_top
% 27.58/4.02      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 27.58/4.02      | v1_xboole_0(X5_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X2_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X4_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1065]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_20,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.02      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.02      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.02      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | ~ v1_funct_1(X3)
% 27.58/4.02      | v1_xboole_0(X5)
% 27.58/4.02      | v1_xboole_0(X2)
% 27.58/4.02      | v1_xboole_0(X4)
% 27.58/4.02      | v1_xboole_0(X1) ),
% 27.58/4.02      inference(cnf_transformation,[],[f76]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1067,plain,
% 27.58/4.02      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 27.58/4.02      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 27.58/4.02      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 27.58/4.02      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 27.58/4.02      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.02      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 27.58/4.02      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 27.58/4.02      | ~ v1_funct_1(X0_53)
% 27.58/4.02      | ~ v1_funct_1(X3_53)
% 27.58/4.02      | v1_xboole_0(X2_53)
% 27.58/4.02      | v1_xboole_0(X1_53)
% 27.58/4.02      | v1_xboole_0(X4_53)
% 27.58/4.02      | v1_xboole_0(X5_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_20]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1856,plain,
% 27.58/4.02      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 27.58/4.02      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 27.58/4.02      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 27.58/4.02      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 27.58/4.02      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 27.58/4.02      | v1_funct_1(X0_53) != iProver_top
% 27.58/4.02      | v1_funct_1(X3_53) != iProver_top
% 27.58/4.02      | v1_xboole_0(X5_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X2_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X4_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_16,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.02      | ~ v1_funct_1(X0)
% 27.58/4.02      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 27.58/4.02      inference(cnf_transformation,[],[f70]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1069,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.02      | ~ v1_funct_1(X0_53)
% 27.58/4.02      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_16]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1854,plain,
% 27.58/4.02      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.58/4.02      | v1_funct_1(X2_53) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1069]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3882,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 27.58/4.02      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 27.58/4.02      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 27.58/4.02      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 27.58/4.02      | v1_funct_1(X5_53) != iProver_top
% 27.58/4.02      | v1_funct_1(X4_53) != iProver_top
% 27.58/4.02      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X3_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X2_53) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1856,c_1854]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_8171,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 27.58/4.02      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 27.58/4.02      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 27.58/4.02      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 27.58/4.02      | v1_funct_1(X5_53) != iProver_top
% 27.58/4.02      | v1_funct_1(X4_53) != iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X3_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X2_53) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1858,c_3882]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15369,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 27.58/4.02      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 27.58/4.02      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 27.58/4.02      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | v1_funct_1(X2_53) != iProver_top
% 27.58/4.02      | v1_funct_1(sK5) != iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK1) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK3) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1859,c_8171]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_38,plain,
% 27.58/4.02      ( v1_xboole_0(sK1) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_47,plain,
% 27.58/4.02      ( v1_funct_1(sK5) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_48,plain,
% 27.58/4.02      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15586,plain,
% 27.58/4.02      ( v1_funct_1(X2_53) != iProver_top
% 27.58/4.02      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 27.58/4.02      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_15369,c_38,c_41,c_47,c_48]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15587,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 27.58/4.02      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 27.58/4.02      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 27.58/4.02      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | v1_funct_1(X2_53) != iProver_top
% 27.58/4.02      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.02      inference(renaming,[status(thm)],[c_15586]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15593,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 27.58/4.02      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 27.58/4.02      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | v1_funct_1(sK4) != iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1862,c_15587]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_44,plain,
% 27.58/4.02      ( v1_funct_1(sK4) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_45,plain,
% 27.58/4.02      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15809,plain,
% 27.58/4.02      ( v1_xboole_0(X0_53) = iProver_top
% 27.58/4.02      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 27.58/4.02      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_15593,c_39,c_44,c_45]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15810,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 27.58/4.02      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.02      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.02      inference(renaming,[status(thm)],[c_15809]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15815,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 27.58/4.02      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.02      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1866,c_15810]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_36,negated_conjecture,
% 27.58/4.02      ( ~ v1_xboole_0(sK0) ),
% 27.58/4.02      inference(cnf_transformation,[],[f77]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_37,plain,
% 27.58/4.02      ( v1_xboole_0(sK0) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_33,negated_conjecture,
% 27.58/4.02      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 27.58/4.02      inference(cnf_transformation,[],[f80]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_40,plain,
% 27.58/4.02      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_15878,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 27.58/4.02      inference(global_propositional_subsumption,
% 27.58/4.02                [status(thm)],
% 27.58/4.02                [c_15815,c_37,c_40]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3774,plain,
% 27.58/4.02      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 27.58/4.02      | v1_funct_1(sK5) != iProver_top ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1859,c_1854]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3988,plain,
% 27.58/4.02      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 27.58/4.02      inference(global_propositional_subsumption,[status(thm)],[c_3774,c_47]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3598,plain,
% 27.58/4.02      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_3594,c_1845]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.58/4.02      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 27.58/4.02      inference(cnf_transformation,[],[f57]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1077,plain,
% 27.58/4.02      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 27.58/4.02      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_3]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1846,plain,
% 27.58/4.02      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 27.58/4.02      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 27.58/4.02      inference(predicate_to_equality,[status(thm)],[c_1077]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2665,plain,
% 27.58/4.02      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 27.58/4.02      inference(superposition,[status(thm)],[c_1866,c_1846]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_23,negated_conjecture,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.02      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.02      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 27.58/4.02      inference(cnf_transformation,[],[f90]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_1064,negated_conjecture,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.02      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.02      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 27.58/4.02      inference(subtyping,[status(esa)],[c_23]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_2856,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.02      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.02      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 27.58/4.02      inference(demodulation,[status(thm)],[c_2665,c_1064]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3618,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.02      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.02      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 27.58/4.02      inference(demodulation,[status(thm)],[c_3598,c_2856]) ).
% 27.58/4.02  
% 27.58/4.02  cnf(c_3991,plain,
% 27.58/4.02      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.02      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.02      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.02      inference(demodulation,[status(thm)],[c_3988,c_3618]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_3775,plain,
% 27.58/4.03      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 27.58/4.03      | v1_funct_1(sK4) != iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_1862,c_1854]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_3993,plain,
% 27.58/4.03      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 27.58/4.03      inference(global_propositional_subsumption,[status(thm)],[c_3775,c_44]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_4039,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.03      inference(demodulation,[status(thm)],[c_3991,c_3993]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_15881,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.03      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.03      inference(demodulation,[status(thm)],[c_15878,c_4039]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_15882,plain,
% 27.58/4.03      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 27.58/4.03      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.03      inference(demodulation,[status(thm)],[c_15881,c_15878]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_19,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_1(X3)
% 27.58/4.03      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X1)
% 27.58/4.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 27.58/4.03      inference(cnf_transformation,[],[f95]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_21,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_1(X3)
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X1) ),
% 27.58/4.03      inference(cnf_transformation,[],[f75]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_198,plain,
% 27.58/4.03      ( ~ v1_funct_1(X3)
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X1)
% 27.58/4.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_19,c_22,c_21,c_20]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_199,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_1(X3)
% 27.58/4.03      | v1_xboole_0(X1)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 27.58/4.03      inference(renaming,[status(thm)],[c_198]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_1050,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 27.58/4.03      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 27.58/4.03      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 27.58/4.03      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 27.58/4.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.03      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 27.58/4.03      | ~ v1_funct_1(X0_53)
% 27.58/4.03      | ~ v1_funct_1(X3_53)
% 27.58/4.03      | v1_xboole_0(X2_53)
% 27.58/4.03      | v1_xboole_0(X1_53)
% 27.58/4.03      | v1_xboole_0(X4_53)
% 27.58/4.03      | v1_xboole_0(X5_53)
% 27.58/4.03      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 27.58/4.03      inference(subtyping,[status(esa)],[c_199]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_1872,plain,
% 27.58/4.03      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 27.58/4.03      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 27.58/4.03      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 27.58/4.03      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.58/4.03      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 27.58/4.03      | v1_funct_1(X2_53) != iProver_top
% 27.58/4.03      | v1_funct_1(X5_53) != iProver_top
% 27.58/4.03      | v1_xboole_0(X3_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X4_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.03      inference(predicate_to_equality,[status(thm)],[c_1050]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_4342,plain,
% 27.58/4.03      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 27.58/4.03      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 27.58/4.03      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | v1_funct_1(X1_53) != iProver_top
% 27.58/4.03      | v1_funct_1(sK5) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X2_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(sK1) = iProver_top
% 27.58/4.03      | v1_xboole_0(sK3) = iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_3988,c_1872]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_49,plain,
% 27.58/4.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 27.58/4.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_4951,plain,
% 27.58/4.03      ( v1_funct_1(X1_53) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 27.58/4.03      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 27.58/4.03      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X2_53) = iProver_top ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_4342,c_38,c_41,c_47,c_48,c_49]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_4952,plain,
% 27.58/4.03      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 27.58/4.03      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | v1_funct_1(X1_53) != iProver_top
% 27.58/4.03      | v1_xboole_0(X2_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.03      inference(renaming,[status(thm)],[c_4951]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_4958,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 27.58/4.03      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 27.58/4.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | v1_funct_1(sK4) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_3993,c_4952]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_46,plain,
% 27.58/4.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 27.58/4.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5060,plain,
% 27.58/4.03      ( v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_4958,c_39,c_44,c_45,c_46]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5061,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.03      inference(renaming,[status(thm)],[c_5060]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5066,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_2665,c_5061]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5067,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(light_normalisation,[status(thm)],[c_5066,c_3598]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5068,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(demodulation,[status(thm)],[c_5067,c_2665]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5069,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(light_normalisation,[status(thm)],[c_5068,c_3598]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5070,plain,
% 27.58/4.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 27.58/4.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 27.58/4.03      | v1_xboole_0(sK0)
% 27.58/4.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.03      inference(predicate_to_equality_rev,[status(thm)],[c_5069]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_18,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_1(X3)
% 27.58/4.03      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X1)
% 27.58/4.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 27.58/4.03      inference(cnf_transformation,[],[f94]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_205,plain,
% 27.58/4.03      ( ~ v1_funct_1(X3)
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X1)
% 27.58/4.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_18,c_22,c_21,c_20]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_206,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0,X1,X2)
% 27.58/4.03      | ~ v1_funct_2(X3,X4,X2)
% 27.58/4.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 27.58/4.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.58/4.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.58/4.03      | ~ v1_funct_1(X0)
% 27.58/4.03      | ~ v1_funct_1(X3)
% 27.58/4.03      | v1_xboole_0(X1)
% 27.58/4.03      | v1_xboole_0(X2)
% 27.58/4.03      | v1_xboole_0(X4)
% 27.58/4.03      | v1_xboole_0(X5)
% 27.58/4.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 27.58/4.03      inference(renaming,[status(thm)],[c_205]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_1049,plain,
% 27.58/4.03      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 27.58/4.03      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 27.58/4.03      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 27.58/4.03      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 27.58/4.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 27.58/4.03      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 27.58/4.03      | ~ v1_funct_1(X0_53)
% 27.58/4.03      | ~ v1_funct_1(X3_53)
% 27.58/4.03      | v1_xboole_0(X2_53)
% 27.58/4.03      | v1_xboole_0(X1_53)
% 27.58/4.03      | v1_xboole_0(X4_53)
% 27.58/4.03      | v1_xboole_0(X5_53)
% 27.58/4.03      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 27.58/4.03      inference(subtyping,[status(esa)],[c_206]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_1873,plain,
% 27.58/4.03      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 27.58/4.03      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 27.58/4.03      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 27.58/4.03      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.58/4.03      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 27.58/4.03      | v1_funct_1(X2_53) != iProver_top
% 27.58/4.03      | v1_funct_1(X5_53) != iProver_top
% 27.58/4.03      | v1_xboole_0(X3_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X1_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X4_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.03      inference(predicate_to_equality,[status(thm)],[c_1049]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_5206,plain,
% 27.58/4.03      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 27.58/4.03      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 27.58/4.03      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | v1_funct_1(X1_53) != iProver_top
% 27.58/4.03      | v1_funct_1(sK5) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X2_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(sK1) = iProver_top
% 27.58/4.03      | v1_xboole_0(sK3) = iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_3988,c_1873]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10447,plain,
% 27.58/4.03      ( v1_funct_1(X1_53) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 27.58/4.03      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 27.58/4.03      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X2_53) = iProver_top ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_5206,c_38,c_41,c_47,c_48,c_49]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10448,plain,
% 27.58/4.03      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 27.58/4.03      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 27.58/4.03      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 27.58/4.03      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 27.58/4.03      | v1_funct_1(X1_53) != iProver_top
% 27.58/4.03      | v1_xboole_0(X2_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.03      inference(renaming,[status(thm)],[c_10447]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10454,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 27.58/4.03      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 27.58/4.03      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | v1_funct_1(sK4) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | v1_xboole_0(sK2) = iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_3993,c_10448]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10494,plain,
% 27.58/4.03      ( v1_xboole_0(X0_53) = iProver_top
% 27.58/4.03      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_10454,c_39,c_44,c_45,c_46]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10495,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 27.58/4.03      | v1_xboole_0(X0_53) = iProver_top ),
% 27.58/4.03      inference(renaming,[status(thm)],[c_10494]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10500,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_2665,c_10495]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10501,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(light_normalisation,[status(thm)],[c_10500,c_3598]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10502,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(demodulation,[status(thm)],[c_10501,c_2665]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10503,plain,
% 27.58/4.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
% 27.58/4.03      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 27.58/4.03      | v1_xboole_0(sK0) = iProver_top ),
% 27.58/4.03      inference(light_normalisation,[status(thm)],[c_10502,c_3598]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_10504,plain,
% 27.58/4.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 27.58/4.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 27.58/4.03      | v1_xboole_0(sK0)
% 27.58/4.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 27.58/4.03      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.03      inference(predicate_to_equality_rev,[status(thm)],[c_10503]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_17467,plain,
% 27.58/4.03      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 27.58/4.03      inference(global_propositional_subsumption,
% 27.58/4.03                [status(thm)],
% 27.58/4.03                [c_15882,c_36,c_33,c_31,c_4039,c_5070,c_10504]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_46863,plain,
% 27.58/4.03      ( k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 27.58/4.03      inference(demodulation,[status(thm)],[c_46649,c_17467]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_46650,plain,
% 27.58/4.03      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 27.58/4.03      inference(superposition,[status(thm)],[c_46438,c_7141]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_46868,plain,
% 27.58/4.03      ( k1_xboole_0 != k1_xboole_0 ),
% 27.58/4.03      inference(light_normalisation,[status(thm)],[c_46863,c_46650]) ).
% 27.58/4.03  
% 27.58/4.03  cnf(c_46869,plain,
% 27.58/4.03      ( $false ),
% 27.58/4.03      inference(equality_resolution_simp,[status(thm)],[c_46868]) ).
% 27.58/4.03  
% 27.58/4.03  
% 27.58/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.58/4.03  
% 27.58/4.03  ------                               Statistics
% 27.58/4.03  
% 27.58/4.03  ------ General
% 27.58/4.03  
% 27.58/4.03  abstr_ref_over_cycles:                  0
% 27.58/4.03  abstr_ref_under_cycles:                 0
% 27.58/4.03  gc_basic_clause_elim:                   0
% 27.58/4.03  forced_gc_time:                         0
% 27.58/4.03  parsing_time:                           0.009
% 27.58/4.03  unif_index_cands_time:                  0.
% 27.58/4.03  unif_index_add_time:                    0.
% 27.58/4.03  orderings_time:                         0.
% 27.58/4.03  out_proof_time:                         0.032
% 27.58/4.03  total_time:                             3.243
% 27.58/4.03  num_of_symbols:                         58
% 27.58/4.03  num_of_terms:                           106810
% 27.58/4.03  
% 27.58/4.03  ------ Preprocessing
% 27.58/4.03  
% 27.58/4.03  num_of_splits:                          0
% 27.58/4.03  num_of_split_atoms:                     0
% 27.58/4.03  num_of_reused_defs:                     0
% 27.58/4.03  num_eq_ax_congr_red:                    14
% 27.58/4.03  num_of_sem_filtered_clauses:            1
% 27.58/4.03  num_of_subtypes:                        2
% 27.58/4.03  monotx_restored_types:                  0
% 27.58/4.03  sat_num_of_epr_types:                   0
% 27.58/4.03  sat_num_of_non_cyclic_types:            0
% 27.58/4.03  sat_guarded_non_collapsed_types:        1
% 27.58/4.03  num_pure_diseq_elim:                    0
% 27.58/4.03  simp_replaced_by:                       0
% 27.58/4.03  res_preprocessed:                       170
% 27.58/4.03  prep_upred:                             0
% 27.58/4.03  prep_unflattend:                        14
% 27.58/4.03  smt_new_axioms:                         0
% 27.58/4.03  pred_elim_cands:                        7
% 27.58/4.03  pred_elim:                              2
% 27.58/4.03  pred_elim_cl:                           3
% 27.58/4.03  pred_elim_cycles:                       6
% 27.58/4.03  merged_defs:                            8
% 27.58/4.03  merged_defs_ncl:                        0
% 27.58/4.03  bin_hyper_res:                          8
% 27.58/4.03  prep_cycles:                            4
% 27.58/4.03  pred_elim_time:                         0.004
% 27.58/4.03  splitting_time:                         0.
% 27.58/4.03  sem_filter_time:                        0.
% 27.58/4.03  monotx_time:                            0.
% 27.58/4.03  subtype_inf_time:                       0.001
% 27.58/4.03  
% 27.58/4.03  ------ Problem properties
% 27.58/4.03  
% 27.58/4.03  clauses:                                33
% 27.58/4.03  conjectures:                            14
% 27.58/4.03  epr:                                    12
% 27.58/4.03  horn:                                   23
% 27.58/4.03  ground:                                 14
% 27.58/4.03  unary:                                  15
% 27.58/4.03  binary:                                 5
% 27.58/4.03  lits:                                   135
% 27.58/4.03  lits_eq:                                17
% 27.58/4.03  fd_pure:                                0
% 27.58/4.03  fd_pseudo:                              0
% 27.58/4.03  fd_cond:                                0
% 27.58/4.03  fd_pseudo_cond:                         1
% 27.58/4.03  ac_symbols:                             0
% 27.58/4.03  
% 27.58/4.03  ------ Propositional Solver
% 27.58/4.03  
% 27.58/4.03  prop_solver_calls:                      39
% 27.58/4.03  prop_fast_solver_calls:                 11271
% 27.58/4.03  smt_solver_calls:                       0
% 27.58/4.03  smt_fast_solver_calls:                  0
% 27.58/4.03  prop_num_of_clauses:                    22504
% 27.58/4.03  prop_preprocess_simplified:             50809
% 27.58/4.03  prop_fo_subsumed:                       1117
% 27.58/4.03  prop_solver_time:                       0.
% 27.58/4.03  smt_solver_time:                        0.
% 27.58/4.03  smt_fast_solver_time:                   0.
% 27.58/4.03  prop_fast_solver_time:                  0.
% 27.58/4.03  prop_unsat_core_time:                   0.
% 27.58/4.03  
% 27.58/4.03  ------ QBF
% 27.58/4.03  
% 27.58/4.03  qbf_q_res:                              0
% 27.58/4.03  qbf_num_tautologies:                    0
% 27.58/4.03  qbf_prep_cycles:                        0
% 27.58/4.03  
% 27.58/4.03  ------ BMC1
% 27.58/4.03  
% 27.58/4.03  bmc1_current_bound:                     -1
% 27.58/4.03  bmc1_last_solved_bound:                 -1
% 27.58/4.03  bmc1_unsat_core_size:                   -1
% 27.58/4.03  bmc1_unsat_core_parents_size:           -1
% 27.58/4.03  bmc1_merge_next_fun:                    0
% 27.58/4.03  bmc1_unsat_core_clauses_time:           0.
% 27.58/4.03  
% 27.58/4.03  ------ Instantiation
% 27.58/4.03  
% 27.58/4.03  inst_num_of_clauses:                    284
% 27.58/4.03  inst_num_in_passive:                    42
% 27.58/4.03  inst_num_in_active:                     2923
% 27.58/4.03  inst_num_in_unprocessed:                44
% 27.58/4.03  inst_num_of_loops:                      3199
% 27.58/4.03  inst_num_of_learning_restarts:          1
% 27.58/4.03  inst_num_moves_active_passive:          272
% 27.58/4.03  inst_lit_activity:                      0
% 27.58/4.03  inst_lit_activity_moves:                2
% 27.58/4.03  inst_num_tautologies:                   0
% 27.58/4.03  inst_num_prop_implied:                  0
% 27.58/4.03  inst_num_existing_simplified:           0
% 27.58/4.03  inst_num_eq_res_simplified:             0
% 27.58/4.03  inst_num_child_elim:                    0
% 27.58/4.03  inst_num_of_dismatching_blockings:      1811
% 27.58/4.03  inst_num_of_non_proper_insts:           4473
% 27.58/4.03  inst_num_of_duplicates:                 0
% 27.58/4.03  inst_inst_num_from_inst_to_res:         0
% 27.58/4.03  inst_dismatching_checking_time:         0.
% 27.58/4.03  
% 27.58/4.03  ------ Resolution
% 27.58/4.03  
% 27.58/4.03  res_num_of_clauses:                     50
% 27.58/4.03  res_num_in_passive:                     50
% 27.58/4.03  res_num_in_active:                      0
% 27.58/4.03  res_num_of_loops:                       174
% 27.58/4.03  res_forward_subset_subsumed:            99
% 27.58/4.03  res_backward_subset_subsumed:           0
% 27.58/4.03  res_forward_subsumed:                   0
% 27.58/4.03  res_backward_subsumed:                  0
% 27.58/4.03  res_forward_subsumption_resolution:     1
% 27.58/4.03  res_backward_subsumption_resolution:    0
% 27.58/4.03  res_clause_to_clause_subsumption:       3339
% 27.58/4.03  res_orphan_elimination:                 0
% 27.58/4.03  res_tautology_del:                      143
% 27.58/4.03  res_num_eq_res_simplified:              0
% 27.58/4.03  res_num_sel_changes:                    0
% 27.58/4.03  res_moves_from_active_to_pass:          0
% 27.58/4.03  
% 27.58/4.03  ------ Superposition
% 27.58/4.03  
% 27.58/4.03  sup_time_total:                         0.
% 27.58/4.03  sup_time_generating:                    0.
% 27.58/4.03  sup_time_sim_full:                      0.
% 27.58/4.03  sup_time_sim_immed:                     0.
% 27.58/4.03  
% 27.58/4.03  sup_num_of_clauses:                     687
% 27.58/4.03  sup_num_in_active:                      524
% 27.58/4.03  sup_num_in_passive:                     163
% 27.58/4.03  sup_num_of_loops:                       639
% 27.58/4.03  sup_fw_superposition:                   775
% 27.58/4.03  sup_bw_superposition:                   337
% 27.58/4.03  sup_immediate_simplified:               613
% 27.58/4.03  sup_given_eliminated:                   0
% 27.58/4.03  comparisons_done:                       0
% 27.58/4.03  comparisons_avoided:                    0
% 27.58/4.03  
% 27.58/4.03  ------ Simplifications
% 27.58/4.03  
% 27.58/4.03  
% 27.58/4.03  sim_fw_subset_subsumed:                 17
% 27.58/4.03  sim_bw_subset_subsumed:                 18
% 27.58/4.03  sim_fw_subsumed:                        249
% 27.58/4.03  sim_bw_subsumed:                        60
% 27.58/4.03  sim_fw_subsumption_res:                 0
% 27.58/4.03  sim_bw_subsumption_res:                 0
% 27.58/4.03  sim_tautology_del:                      0
% 27.58/4.03  sim_eq_tautology_del:                   12
% 27.58/4.03  sim_eq_res_simp:                        3
% 27.58/4.03  sim_fw_demodulated:                     433
% 27.58/4.03  sim_bw_demodulated:                     52
% 27.58/4.03  sim_light_normalised:                   225
% 27.58/4.03  sim_joinable_taut:                      0
% 27.58/4.03  sim_joinable_simp:                      0
% 27.58/4.03  sim_ac_normalised:                      0
% 27.58/4.03  sim_smt_subsumption:                    0
% 27.58/4.03  
%------------------------------------------------------------------------------
