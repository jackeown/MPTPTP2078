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
% DateTime   : Thu Dec  3 12:21:24 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  273 (5392 expanded)
%              Number of clauses        :  171 (1349 expanded)
%              Number of leaves         :   29 (1903 expanded)
%              Depth                    :   32
%              Number of atoms          : 1273 (57704 expanded)
%              Number of equality atoms :  516 (13306 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4
          | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK6,X3,X1)
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5
              | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK5,X2,X1)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4
                  | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
                & v1_funct_2(X5,sK4,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4
                      | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
                & v1_funct_2(X4,sK3,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK3,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2)))
                        & v1_funct_2(X5,X3,sK2)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
                    & v1_funct_2(X4,X2,sK2)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
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
                          ( ( k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK1))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK1))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,
    ( ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    & v1_funct_2(sK6,sK4,sK2)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    & v1_funct_2(sK5,sK3,sK2)
    & v1_funct_1(sK5)
    & r1_subset_1(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f53,f68,f67,f66,f65,f64,f63])).

fof(f109,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f69])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f75])).

fof(f116,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f69])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f114,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

fof(f113,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f69])).

fof(f111,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f69])).

fof(f21,axiom,(
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

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f49])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f125,plain,(
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
    inference(equality_resolution,[],[f98])).

fof(f22,axiom,(
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

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f105,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f106,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

fof(f112,plain,(
    v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f108,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f115,plain,(
    v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f69])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f110,plain,(
    r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f70,f75])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f77,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f124,plain,(
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
    inference(equality_resolution,[],[f99])).

fof(f117,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f69])).

fof(f107,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2524,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2548,plain,
    ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4397,plain,
    ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
    inference(superposition,[status(thm)],[c_2524,c_2548])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2530,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2535,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6821,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2535])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3075,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3505,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | ~ v1_funct_1(sK6)
    | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3075])).

cnf(c_6915,plain,
    ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6821,c_36,c_34,c_3505])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2527,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6822,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_2535])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3080,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3510,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_3080])).

cnf(c_6921,plain,
    ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6822,c_39,c_37,c_3510])).

cnf(c_29,plain,
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
    inference(cnf_transformation,[],[f125])).

cnf(c_32,plain,
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
    inference(cnf_transformation,[],[f101])).

cnf(c_31,plain,
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
    inference(cnf_transformation,[],[f102])).

cnf(c_30,plain,
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
    inference(cnf_transformation,[],[f103])).

cnf(c_252,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_32,c_31,c_30])).

cnf(c_253,plain,
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
    inference(renaming,[status(thm)],[c_252])).

cnf(c_2518,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2547,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2803,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
    | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
    | v1_funct_2(X5,X4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2518,c_2547])).

cnf(c_9916,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6921,c_2803])).

cnf(c_45,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_48,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_49,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_54,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK2) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_55,plain,
    ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_56,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_13031,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9916,c_48,c_49,c_54,c_55,c_56])).

cnf(c_13032,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_13031])).

cnf(c_13045,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6915,c_13032])).

cnf(c_42,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_51,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_57,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_58,plain,
    ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_59,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13431,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13045,c_51,c_57,c_58,c_59])).

cnf(c_13441,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4397,c_13431])).

cnf(c_18,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,negated_conjecture,
    ( r1_subset_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_641,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_40])).

cnf(c_642,plain,
    ( r1_xboole_0(sK3,sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_644,plain,
    ( r1_xboole_0(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_642,c_44,c_42])).

cnf(c_2515,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_644])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2549,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3757,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2515,c_2549])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_25,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_600,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_20,c_25])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_25,c_20,c_19])).

cnf(c_603,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_602])).

cnf(c_654,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_22,c_603])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_25,c_22,c_20,c_19])).

cnf(c_657,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_656])).

cnf(c_2514,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_3550,plain,
    ( k1_relat_1(sK6) = sK4
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2514])).

cnf(c_3663,plain,
    ( k1_relat_1(sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3550,c_48,c_57,c_58])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2542,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5193,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_2542])).

cnf(c_2979,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2980,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2979])).

cnf(c_5686,plain,
    ( r1_xboole_0(X0,sK4) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5193,c_59,c_2980])).

cnf(c_5687,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_5686])).

cnf(c_5695,plain,
    ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2515,c_5687])).

cnf(c_2537,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3716,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2537])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_585,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k9_relat_1(k7_relat_1(X0,X1),X3) = k9_relat_1(X0,X3)
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_586,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_585])).

cnf(c_2516,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_586])).

cnf(c_4186,plain,
    ( k9_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k9_relat_1(sK6,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3716,c_2516])).

cnf(c_5813,plain,
    ( k9_relat_1(sK6,k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5695,c_4186])).

cnf(c_3546,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_2514])).

cnf(c_3639,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3546,c_48,c_54,c_55])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2539,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5025,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(sK3,X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3639,c_2539])).

cnf(c_2982,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2983,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2982])).

cnf(c_5551,plain,
    ( r1_xboole_0(sK3,X0) != iProver_top
    | k7_relat_1(sK5,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5025,c_56,c_2983])).

cnf(c_5552,plain,
    ( k7_relat_1(sK5,X0) = k1_xboole_0
    | r1_xboole_0(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5551])).

cnf(c_5559,plain,
    ( k7_relat_1(sK5,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2515,c_5552])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2546,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5673,plain,
    ( v1_relat_1(sK5) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_2546])).

cnf(c_7516,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5673,c_56,c_2983])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2545,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7522,plain,
    ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7516,c_2545])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_12,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7524,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7522,c_11,c_12])).

cnf(c_8020,plain,
    ( k9_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5813,c_7524])).

cnf(c_8,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2543,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8024,plain,
    ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8020,c_2543])).

cnf(c_8025,plain,
    ( r1_xboole_0(sK4,k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8024,c_3663])).

cnf(c_8028,plain,
    ( r1_xboole_0(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8025,c_59,c_2980])).

cnf(c_5024,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(sK4,X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_2539])).

cnf(c_5542,plain,
    ( r1_xboole_0(sK4,X0) != iProver_top
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5024,c_59,c_2980])).

cnf(c_5543,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(sK4,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5542])).

cnf(c_8036,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8028,c_5543])).

cnf(c_13442,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13441,c_3757,c_8036])).

cnf(c_13443,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13442,c_4397])).

cnf(c_3717,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2527,c_2537])).

cnf(c_4187,plain,
    ( k9_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3717,c_2516])).

cnf(c_5674,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5559,c_4187])).

cnf(c_7766,plain,
    ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5674,c_7524])).

cnf(c_7770,plain,
    ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7766,c_2543])).

cnf(c_7771,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7770,c_3639])).

cnf(c_7774,plain,
    ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7771,c_56,c_2983])).

cnf(c_7781,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7774,c_5552])).

cnf(c_13444,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13443,c_3757,c_7781])).

cnf(c_13445,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13444])).

cnf(c_28,plain,
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
    inference(cnf_transformation,[],[f124])).

cnf(c_259,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_32,c_31,c_30])).

cnf(c_260,plain,
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
    inference(renaming,[status(thm)],[c_259])).

cnf(c_2517,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_260])).

cnf(c_2775,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
    | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
    | v1_funct_2(X5,X4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2517,c_2547])).

cnf(c_8113,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | v1_funct_2(sK5,sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6921,c_2775])).

cnf(c_10489,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8113,c_48,c_49,c_54,c_55,c_56])).

cnf(c_10490,plain,
    ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
    | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
    | v1_funct_2(X1,X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_10489])).

cnf(c_10503,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | v1_funct_2(sK6,sK4,sK2) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6915,c_10490])).

cnf(c_10835,plain,
    ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10503,c_51,c_57,c_58,c_59])).

cnf(c_10845,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4397,c_10835])).

cnf(c_10846,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10845,c_3757,c_8036])).

cnf(c_10847,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10846,c_4397])).

cnf(c_10848,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10847,c_3757,c_7781])).

cnf(c_10849,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
    | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10848])).

cnf(c_33,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_4571,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
    inference(demodulation,[status(thm)],[c_4397,c_33])).

cnf(c_4572,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4571,c_3757])).

cnf(c_6919,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6915,c_4572])).

cnf(c_7215,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6919,c_6921])).

cnf(c_7889,plain,
    ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
    | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7781,c_7215])).

cnf(c_1593,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_6020,plain,
    ( k9_relat_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k9_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_6021,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6020])).

cnf(c_3705,plain,
    ( k9_relat_1(sK6,X0) != X1
    | k9_relat_1(sK6,X0) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1593])).

cnf(c_5760,plain,
    ( k9_relat_1(sK6,X0) != k9_relat_1(X1,X2)
    | k9_relat_1(sK6,X0) = k1_xboole_0
    | k1_xboole_0 != k9_relat_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_3705])).

cnf(c_5762,plain,
    ( k9_relat_1(sK6,k1_xboole_0) != k9_relat_1(k1_xboole_0,k1_xboole_0)
    | k9_relat_1(sK6,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5760])).

cnf(c_3164,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6)
    | k7_relat_1(sK6,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3199,plain,
    ( k7_relat_1(sK6,X0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK6),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3164])).

cnf(c_3201,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3199])).

cnf(c_3165,plain,
    ( r1_xboole_0(k1_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6)
    | k9_relat_1(sK6,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3195,plain,
    ( k9_relat_1(sK6,X0) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK6),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3165])).

cnf(c_3197,plain,
    ( k9_relat_1(sK6,k1_xboole_0) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3195])).

cnf(c_1592,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1627,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1592])).

cnf(c_52,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13445,c_10849,c_7889,c_7524,c_6021,c_5813,c_5762,c_3201,c_3197,c_2980,c_1627,c_59,c_52,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.76/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/0.98  
% 3.76/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.76/0.98  
% 3.76/0.98  ------  iProver source info
% 3.76/0.98  
% 3.76/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.76/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.76/0.98  git: non_committed_changes: false
% 3.76/0.98  git: last_make_outside_of_git: false
% 3.76/0.98  
% 3.76/0.98  ------ 
% 3.76/0.98  ------ Parsing...
% 3.76/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.76/0.98  
% 3.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.76/0.98  
% 3.76/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.76/0.98  
% 3.76/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.76/0.98  ------ Proving...
% 3.76/0.98  ------ Problem Properties 
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  clauses                                 40
% 3.76/0.98  conjectures                             13
% 3.76/0.98  EPR                                     9
% 3.76/0.98  Horn                                    32
% 3.76/0.98  unary                                   15
% 3.76/0.98  binary                                  8
% 3.76/0.98  lits                                    150
% 3.76/0.98  lits eq                                 28
% 3.76/0.98  fd_pure                                 0
% 3.76/0.98  fd_pseudo                               0
% 3.76/0.98  fd_cond                                 3
% 3.76/0.98  fd_pseudo_cond                          1
% 3.76/0.98  AC symbols                              0
% 3.76/0.98  
% 3.76/0.98  ------ Input Options Time Limit: Unbounded
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  ------ 
% 3.76/0.98  Current options:
% 3.76/0.98  ------ 
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  ------ Proving...
% 3.76/0.98  
% 3.76/0.98  
% 3.76/0.98  % SZS status Theorem for theBenchmark.p
% 3.76/0.98  
% 3.76/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.76/0.98  
% 3.76/0.98  fof(f23,conjecture,(
% 3.76/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f24,negated_conjecture,(
% 3.76/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.76/0.98    inference(negated_conjecture,[],[f23])).
% 3.76/0.98  
% 3.76/0.98  fof(f52,plain,(
% 3.76/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f24])).
% 3.76/0.98  
% 3.76/0.98  fof(f53,plain,(
% 3.76/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.76/0.98    inference(flattening,[],[f52])).
% 3.76/0.98  
% 3.76/0.98  fof(f68,plain,(
% 3.76/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X3) != sK6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK6),X2) != X4 | k2_partfun1(X3,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK6,X3,X1) & v1_funct_1(sK6))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f67,plain,(
% 3.76/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK5,X5),X2) != sK5 | k2_partfun1(X2,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK5,X2,X1) & v1_funct_1(sK5))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f66,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),sK4) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK4),X1,k1_tmap_1(X0,X1,X2,sK4,X4,X5),X2) != X4 | k2_partfun1(sK4,X1,X5,k9_subset_1(X0,X2,sK4)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK4))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X5,sK4,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK4) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f65,plain,(
% 3.76/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK3,X3),X1,k1_tmap_1(X0,X1,sK3,X3,X4,X5),sK3) != X4 | k2_partfun1(sK3,X1,X4,k9_subset_1(X0,sK3,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK3,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X4,sK3,X1) & v1_funct_1(X4)) & r1_subset_1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f64,plain,(
% 3.76/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK2,k1_tmap_1(X0,sK2,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK2,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK2,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK2))) & v1_funct_2(X5,X3,sK2) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) & v1_funct_2(X4,X2,sK2) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK2))) )),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f63,plain,(
% 3.76/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK1,X2,X3),X1,k1_tmap_1(sK1,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK1,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK1,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK1)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 3.76/0.98    introduced(choice_axiom,[])).
% 3.76/0.98  
% 3.76/0.98  fof(f69,plain,(
% 3.76/0.98    ((((((k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) & v1_funct_2(sK6,sK4,sK2) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) & v1_funct_2(sK5,sK3,sK2) & v1_funct_1(sK5)) & r1_subset_1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 3.76/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f53,f68,f67,f66,f65,f64,f63])).
% 3.76/0.98  
% 3.76/0.98  fof(f109,plain,(
% 3.76/0.98    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f3,axiom,(
% 3.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f27,plain,(
% 3.76/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.76/0.98    inference(ennf_transformation,[],[f3])).
% 3.76/0.98  
% 3.76/0.98  fof(f73,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f27])).
% 3.76/0.98  
% 3.76/0.98  fof(f5,axiom,(
% 3.76/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f75,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f5])).
% 3.76/0.98  
% 3.76/0.98  fof(f120,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.76/0.98    inference(definition_unfolding,[],[f73,f75])).
% 3.76/0.98  
% 3.76/0.98  fof(f116,plain,(
% 3.76/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f20,axiom,(
% 3.76/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f46,plain,(
% 3.76/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.76/0.98    inference(ennf_transformation,[],[f20])).
% 3.76/0.98  
% 3.76/0.98  fof(f47,plain,(
% 3.76/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.76/0.98    inference(flattening,[],[f46])).
% 3.76/0.98  
% 3.76/0.98  fof(f97,plain,(
% 3.76/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f47])).
% 3.76/0.98  
% 3.76/0.98  fof(f114,plain,(
% 3.76/0.98    v1_funct_1(sK6)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f113,plain,(
% 3.76/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f111,plain,(
% 3.76/0.98    v1_funct_1(sK5)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f21,axiom,(
% 3.76/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f48,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f21])).
% 3.76/0.98  
% 3.76/0.98  fof(f49,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.76/0.98    inference(flattening,[],[f48])).
% 3.76/0.98  
% 3.76/0.98  fof(f61,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.76/0.98    inference(nnf_transformation,[],[f49])).
% 3.76/0.98  
% 3.76/0.98  fof(f62,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.76/0.98    inference(flattening,[],[f61])).
% 3.76/0.98  
% 3.76/0.98  fof(f98,plain,(
% 3.76/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f62])).
% 3.76/0.98  
% 3.76/0.98  fof(f125,plain,(
% 3.76/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(equality_resolution,[],[f98])).
% 3.76/0.98  
% 3.76/0.98  fof(f22,axiom,(
% 3.76/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f50,plain,(
% 3.76/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.76/0.98    inference(ennf_transformation,[],[f22])).
% 3.76/0.98  
% 3.76/0.98  fof(f51,plain,(
% 3.76/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.76/0.98    inference(flattening,[],[f50])).
% 3.76/0.98  
% 3.76/0.98  fof(f101,plain,(
% 3.76/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f51])).
% 3.76/0.98  
% 3.76/0.98  fof(f102,plain,(
% 3.76/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f51])).
% 3.76/0.98  
% 3.76/0.98  fof(f103,plain,(
% 3.76/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f51])).
% 3.76/0.98  
% 3.76/0.98  fof(f4,axiom,(
% 3.76/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f28,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f4])).
% 3.76/0.98  
% 3.76/0.98  fof(f74,plain,(
% 3.76/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f28])).
% 3.76/0.98  
% 3.76/0.98  fof(f105,plain,(
% 3.76/0.98    ~v1_xboole_0(sK2)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f106,plain,(
% 3.76/0.98    ~v1_xboole_0(sK3)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f112,plain,(
% 3.76/0.98    v1_funct_2(sK5,sK3,sK2)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f108,plain,(
% 3.76/0.98    ~v1_xboole_0(sK4)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f115,plain,(
% 3.76/0.98    v1_funct_2(sK6,sK4,sK2)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f14,axiom,(
% 3.76/0.98    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f37,plain,(
% 3.76/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.76/0.98    inference(ennf_transformation,[],[f14])).
% 3.76/0.98  
% 3.76/0.98  fof(f38,plain,(
% 3.76/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.76/0.98    inference(flattening,[],[f37])).
% 3.76/0.98  
% 3.76/0.98  fof(f57,plain,(
% 3.76/0.98    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.76/0.98    inference(nnf_transformation,[],[f38])).
% 3.76/0.98  
% 3.76/0.98  fof(f88,plain,(
% 3.76/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f57])).
% 3.76/0.98  
% 3.76/0.98  fof(f110,plain,(
% 3.76/0.98    r1_subset_1(sK3,sK4)),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f1,axiom,(
% 3.76/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f54,plain,(
% 3.76/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.76/0.98    inference(nnf_transformation,[],[f1])).
% 3.76/0.98  
% 3.76/0.98  fof(f70,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f54])).
% 3.76/0.98  
% 3.76/0.98  fof(f119,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.76/0.98    inference(definition_unfolding,[],[f70,f75])).
% 3.76/0.98  
% 3.76/0.98  fof(f18,axiom,(
% 3.76/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f42,plain,(
% 3.76/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.76/0.98    inference(ennf_transformation,[],[f18])).
% 3.76/0.98  
% 3.76/0.98  fof(f43,plain,(
% 3.76/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.76/0.98    inference(flattening,[],[f42])).
% 3.76/0.98  
% 3.76/0.98  fof(f94,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f43])).
% 3.76/0.98  
% 3.76/0.98  fof(f16,axiom,(
% 3.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f26,plain,(
% 3.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.76/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.76/0.98  
% 3.76/0.98  fof(f40,plain,(
% 3.76/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.98    inference(ennf_transformation,[],[f26])).
% 3.76/0.98  
% 3.76/0.98  fof(f91,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f40])).
% 3.76/0.98  
% 3.76/0.98  fof(f19,axiom,(
% 3.76/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f44,plain,(
% 3.76/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.76/0.98    inference(ennf_transformation,[],[f19])).
% 3.76/0.98  
% 3.76/0.98  fof(f45,plain,(
% 3.76/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.76/0.98    inference(flattening,[],[f44])).
% 3.76/0.98  
% 3.76/0.98  fof(f60,plain,(
% 3.76/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.76/0.98    inference(nnf_transformation,[],[f45])).
% 3.76/0.98  
% 3.76/0.98  fof(f95,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f60])).
% 3.76/0.98  
% 3.76/0.98  fof(f15,axiom,(
% 3.76/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f39,plain,(
% 3.76/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.76/0.98    inference(ennf_transformation,[],[f15])).
% 3.76/0.98  
% 3.76/0.98  fof(f90,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.76/0.98    inference(cnf_transformation,[],[f39])).
% 3.76/0.98  
% 3.76/0.98  fof(f10,axiom,(
% 3.76/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f33,plain,(
% 3.76/0.98    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f10])).
% 3.76/0.98  
% 3.76/0.98  fof(f81,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f33])).
% 3.76/0.98  
% 3.76/0.98  fof(f2,axiom,(
% 3.76/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f72,plain,(
% 3.76/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f2])).
% 3.76/0.98  
% 3.76/0.98  fof(f9,axiom,(
% 3.76/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f32,plain,(
% 3.76/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f9])).
% 3.76/0.98  
% 3.76/0.98  fof(f80,plain,(
% 3.76/0.98    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f32])).
% 3.76/0.98  
% 3.76/0.98  fof(f13,axiom,(
% 3.76/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f36,plain,(
% 3.76/0.98    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.76/0.98    inference(ennf_transformation,[],[f13])).
% 3.76/0.98  
% 3.76/0.98  fof(f56,plain,(
% 3.76/0.98    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.76/0.98    inference(nnf_transformation,[],[f36])).
% 3.76/0.98  
% 3.76/0.98  fof(f87,plain,(
% 3.76/0.98    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f56])).
% 3.76/0.98  
% 3.76/0.98  fof(f6,axiom,(
% 3.76/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f29,plain,(
% 3.76/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f6])).
% 3.76/0.98  
% 3.76/0.98  fof(f76,plain,(
% 3.76/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f29])).
% 3.76/0.98  
% 3.76/0.98  fof(f7,axiom,(
% 3.76/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f30,plain,(
% 3.76/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.76/0.98    inference(ennf_transformation,[],[f7])).
% 3.76/0.98  
% 3.76/0.98  fof(f77,plain,(
% 3.76/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f30])).
% 3.76/0.98  
% 3.76/0.98  fof(f11,axiom,(
% 3.76/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f83,plain,(
% 3.76/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.76/0.98    inference(cnf_transformation,[],[f11])).
% 3.76/0.98  
% 3.76/0.98  fof(f82,plain,(
% 3.76/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.76/0.98    inference(cnf_transformation,[],[f11])).
% 3.76/0.98  
% 3.76/0.98  fof(f8,axiom,(
% 3.76/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.76/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.76/0.98  
% 3.76/0.98  fof(f31,plain,(
% 3.76/0.98    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.76/0.98    inference(ennf_transformation,[],[f8])).
% 3.76/0.98  
% 3.76/0.98  fof(f55,plain,(
% 3.76/0.98    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.76/0.98    inference(nnf_transformation,[],[f31])).
% 3.76/0.98  
% 3.76/0.98  fof(f78,plain,(
% 3.76/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f55])).
% 3.76/0.98  
% 3.76/0.98  fof(f99,plain,(
% 3.76/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(cnf_transformation,[],[f62])).
% 3.76/0.98  
% 3.76/0.98  fof(f124,plain,(
% 3.76/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.76/0.98    inference(equality_resolution,[],[f99])).
% 3.76/0.98  
% 3.76/0.98  fof(f117,plain,(
% 3.76/0.98    k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6 | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5 | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4))),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  fof(f107,plain,(
% 3.76/0.98    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 3.76/0.98    inference(cnf_transformation,[],[f69])).
% 3.76/0.98  
% 3.76/0.98  cnf(c_41,negated_conjecture,
% 3.76/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 3.76/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2524,plain,
% 3.76/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/0.98      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 3.76/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2548,plain,
% 3.76/0.98      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
% 3.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4397,plain,
% 3.76/0.98      ( k9_subset_1(sK1,X0,sK4) = k1_setfam_1(k2_tarski(X0,sK4)) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2524,c_2548]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_34,negated_conjecture,
% 3.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) ),
% 3.76/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2530,plain,
% 3.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_26,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.76/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2535,plain,
% 3.76/0.98      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_6821,plain,
% 3.76/0.98      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0)
% 3.76/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2530,c_2535]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_36,negated_conjecture,
% 3.76/0.98      ( v1_funct_1(sK6) ),
% 3.76/0.98      inference(cnf_transformation,[],[f114]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3075,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/0.98      | ~ v1_funct_1(sK6)
% 3.76/0.98      | k2_partfun1(X0,X1,sK6,X2) = k7_relat_1(sK6,X2) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3505,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.76/0.98      | ~ v1_funct_1(sK6)
% 3.76/0.98      | k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_3075]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_6915,plain,
% 3.76/0.98      ( k2_partfun1(sK4,sK2,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_6821,c_36,c_34,c_3505]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_37,negated_conjecture,
% 3.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) ),
% 3.76/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2527,plain,
% 3.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_6822,plain,
% 3.76/0.98      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0)
% 3.76/0.98      | v1_funct_1(sK5) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2527,c_2535]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_39,negated_conjecture,
% 3.76/0.98      ( v1_funct_1(sK5) ),
% 3.76/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3080,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.76/0.98      | ~ v1_funct_1(sK5)
% 3.76/0.98      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3510,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.76/0.98      | ~ v1_funct_1(sK5)
% 3.76/0.98      | k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_3080]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_6921,plain,
% 3.76/0.98      ( k2_partfun1(sK3,sK2,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_6822,c_39,c_37,c_3510]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_29,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.98      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.76/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.98      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | ~ v1_funct_1(X3)
% 3.76/0.98      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.76/0.98      | v1_xboole_0(X5)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | v1_xboole_0(X4)
% 3.76/0.98      | v1_xboole_0(X1)
% 3.76/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.76/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_32,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | ~ v1_funct_1(X3)
% 3.76/0.98      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.76/0.98      | v1_xboole_0(X5)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | v1_xboole_0(X4)
% 3.76/0.98      | v1_xboole_0(X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_31,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.98      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.76/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | ~ v1_funct_1(X3)
% 3.76/0.98      | v1_xboole_0(X5)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | v1_xboole_0(X4)
% 3.76/0.98      | v1_xboole_0(X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_30,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.98      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | ~ v1_funct_1(X3)
% 3.76/0.98      | v1_xboole_0(X5)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | v1_xboole_0(X4)
% 3.76/0.98      | v1_xboole_0(X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_252,plain,
% 3.76/0.98      ( ~ v1_funct_1(X3)
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.98      | v1_xboole_0(X5)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | v1_xboole_0(X4)
% 3.76/0.98      | v1_xboole_0(X1)
% 3.76/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_29,c_32,c_31,c_30]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_253,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | ~ v1_funct_1(X3)
% 3.76/0.98      | v1_xboole_0(X1)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | v1_xboole_0(X4)
% 3.76/0.98      | v1_xboole_0(X5)
% 3.76/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_252]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2518,plain,
% 3.76/0.98      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.76/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.76/0.98      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.76/0.98      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.76/0.98      | v1_funct_1(X2) != iProver_top
% 3.76/0.98      | v1_funct_1(X5) != iProver_top
% 3.76/0.98      | v1_xboole_0(X3) = iProver_top
% 3.76/0.98      | v1_xboole_0(X1) = iProver_top
% 3.76/0.98      | v1_xboole_0(X4) = iProver_top
% 3.76/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.76/0.98      | ~ v1_xboole_0(X1)
% 3.76/0.98      | v1_xboole_0(X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2547,plain,
% 3.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.76/0.98      | v1_xboole_0(X1) != iProver_top
% 3.76/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2803,plain,
% 3.76/0.98      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 3.76/0.98      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.76/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.98      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.76/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/0.98      | v1_funct_1(X5) != iProver_top
% 3.76/0.98      | v1_funct_1(X2) != iProver_top
% 3.76/0.98      | v1_xboole_0(X0) = iProver_top
% 3.76/0.98      | v1_xboole_0(X1) = iProver_top
% 3.76/0.98      | v1_xboole_0(X4) = iProver_top ),
% 3.76/0.98      inference(forward_subsumption_resolution,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_2518,c_2547]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_9916,plain,
% 3.76/0.98      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 3.76/0.98      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.76/0.98      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.76/0.98      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.98      | v1_funct_1(X1) != iProver_top
% 3.76/0.98      | v1_funct_1(sK5) != iProver_top
% 3.76/0.98      | v1_xboole_0(X0) = iProver_top
% 3.76/0.98      | v1_xboole_0(sK2) = iProver_top
% 3.76/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_6921,c_2803]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_45,negated_conjecture,
% 3.76/0.98      ( ~ v1_xboole_0(sK2) ),
% 3.76/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_48,plain,
% 3.76/0.98      ( v1_xboole_0(sK2) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_44,negated_conjecture,
% 3.76/0.98      ( ~ v1_xboole_0(sK3) ),
% 3.76/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_49,plain,
% 3.76/0.98      ( v1_xboole_0(sK3) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_54,plain,
% 3.76/0.98      ( v1_funct_1(sK5) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_38,negated_conjecture,
% 3.76/0.98      ( v1_funct_2(sK5,sK3,sK2) ),
% 3.76/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_55,plain,
% 3.76/0.98      ( v1_funct_2(sK5,sK3,sK2) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_56,plain,
% 3.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13031,plain,
% 3.76/0.98      ( v1_funct_1(X1) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.98      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.76/0.98      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 3.76/0.98      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.76/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_9916,c_48,c_49,c_54,c_55,c_56]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13032,plain,
% 3.76/0.98      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 3.76/0.98      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),sK3) = sK5
% 3.76/0.98      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.98      | v1_funct_1(X1) != iProver_top
% 3.76/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_13031]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13045,plain,
% 3.76/0.98      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.98      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 3.76/0.98      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.76/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.76/0.98      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.76/0.98      | v1_funct_1(sK6) != iProver_top
% 3.76/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_6915,c_13032]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_42,negated_conjecture,
% 3.76/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.76/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_51,plain,
% 3.76/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_57,plain,
% 3.76/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_35,negated_conjecture,
% 3.76/0.98      ( v1_funct_2(sK6,sK4,sK2) ),
% 3.76/0.98      inference(cnf_transformation,[],[f115]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_58,plain,
% 3.76/0.98      ( v1_funct_2(sK6,sK4,sK2) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_59,plain,
% 3.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13431,plain,
% 3.76/0.98      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.98      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 3.76/0.98      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_13045,c_51,c_57,c_58,c_59]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13441,plain,
% 3.76/0.98      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.98      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 3.76/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_4397,c_13431]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_18,plain,
% 3.76/0.98      ( ~ r1_subset_1(X0,X1)
% 3.76/0.98      | r1_xboole_0(X0,X1)
% 3.76/0.98      | v1_xboole_0(X0)
% 3.76/0.98      | v1_xboole_0(X1) ),
% 3.76/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_40,negated_conjecture,
% 3.76/0.98      ( r1_subset_1(sK3,sK4) ),
% 3.76/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_641,plain,
% 3.76/0.98      ( r1_xboole_0(X0,X1)
% 3.76/0.98      | v1_xboole_0(X0)
% 3.76/0.98      | v1_xboole_0(X1)
% 3.76/0.98      | sK4 != X1
% 3.76/0.98      | sK3 != X0 ),
% 3.76/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_40]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_642,plain,
% 3.76/0.98      ( r1_xboole_0(sK3,sK4) | v1_xboole_0(sK4) | v1_xboole_0(sK3) ),
% 3.76/0.98      inference(unflattening,[status(thm)],[c_641]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_644,plain,
% 3.76/0.98      ( r1_xboole_0(sK3,sK4) ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_642,c_44,c_42]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2515,plain,
% 3.76/0.98      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_644]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_1,plain,
% 3.76/0.98      ( ~ r1_xboole_0(X0,X1)
% 3.76/0.98      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.76/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2549,plain,
% 3.76/0.98      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3757,plain,
% 3.76/0.98      ( k1_setfam_1(k2_tarski(sK3,sK4)) = k1_xboole_0 ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2515,c_2549]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_22,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | v1_partfun1(X0,X1)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | v1_xboole_0(X2) ),
% 3.76/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_20,plain,
% 3.76/0.98      ( v4_relat_1(X0,X1)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.76/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_25,plain,
% 3.76/0.98      ( ~ v1_partfun1(X0,X1)
% 3.76/0.98      | ~ v4_relat_1(X0,X1)
% 3.76/0.98      | ~ v1_relat_1(X0)
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_600,plain,
% 3.76/0.98      ( ~ v1_partfun1(X0,X1)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ v1_relat_1(X0)
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(resolution,[status(thm)],[c_20,c_25]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_19,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | v1_relat_1(X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_602,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ v1_partfun1(X0,X1)
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_600,c_25,c_20,c_19]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_603,plain,
% 3.76/0.98      ( ~ v1_partfun1(X0,X1)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_602]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_654,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(resolution,[status(thm)],[c_22,c_603]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_656,plain,
% 3.76/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_654,c_25,c_22,c_20,c_19]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_657,plain,
% 3.76/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.98      | ~ v1_funct_1(X0)
% 3.76/0.98      | v1_xboole_0(X2)
% 3.76/0.98      | k1_relat_1(X0) = X1 ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_656]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2514,plain,
% 3.76/0.98      ( k1_relat_1(X0) = X1
% 3.76/0.98      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.76/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.76/0.98      | v1_funct_1(X0) != iProver_top
% 3.76/0.98      | v1_xboole_0(X2) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3550,plain,
% 3.76/0.98      ( k1_relat_1(sK6) = sK4
% 3.76/0.98      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.76/0.98      | v1_funct_1(sK6) != iProver_top
% 3.76/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2530,c_2514]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3663,plain,
% 3.76/0.98      ( k1_relat_1(sK6) = sK4 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_3550,c_48,c_57,c_58]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_10,plain,
% 3.76/0.98      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.76/0.98      | ~ v1_relat_1(X1)
% 3.76/0.98      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.76/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2542,plain,
% 3.76/0.98      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 3.76/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5193,plain,
% 3.76/0.98      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(X0,sK4) != iProver_top
% 3.76/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_3663,c_2542]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2979,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2)))
% 3.76/0.98      | v1_relat_1(sK6) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2980,plain,
% 3.76/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.76/0.98      | v1_relat_1(sK6) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_2979]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5686,plain,
% 3.76/0.98      ( r1_xboole_0(X0,sK4) != iProver_top
% 3.76/0.98      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_5193,c_59,c_2980]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5687,plain,
% 3.76/0.98      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(X0,sK4) != iProver_top ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_5686]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5695,plain,
% 3.76/0.98      ( k7_relat_1(sK6,sK3) = k1_xboole_0 ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2515,c_5687]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2537,plain,
% 3.76/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.76/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3716,plain,
% 3.76/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2530,c_2537]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2,plain,
% 3.76/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_9,plain,
% 3.76/0.98      ( ~ r1_tarski(X0,X1)
% 3.76/0.98      | ~ v1_relat_1(X2)
% 3.76/0.98      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_585,plain,
% 3.76/0.98      ( ~ v1_relat_1(X0)
% 3.76/0.98      | X1 != X2
% 3.76/0.98      | k9_relat_1(k7_relat_1(X0,X1),X3) = k9_relat_1(X0,X3)
% 3.76/0.98      | k1_xboole_0 != X3 ),
% 3.76/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_586,plain,
% 3.76/0.98      ( ~ v1_relat_1(X0)
% 3.76/0.98      | k9_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0) ),
% 3.76/0.98      inference(unflattening,[status(thm)],[c_585]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2516,plain,
% 3.76/0.98      ( k9_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k9_relat_1(X0,k1_xboole_0)
% 3.76/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_586]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4186,plain,
% 3.76/0.98      ( k9_relat_1(k7_relat_1(sK6,X0),k1_xboole_0) = k9_relat_1(sK6,k1_xboole_0) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_3716,c_2516]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5813,plain,
% 3.76/0.98      ( k9_relat_1(sK6,k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_5695,c_4186]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3546,plain,
% 3.76/0.98      ( k1_relat_1(sK5) = sK3
% 3.76/0.98      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.76/0.98      | v1_funct_1(sK5) != iProver_top
% 3.76/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2527,c_2514]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3639,plain,
% 3.76/0.98      ( k1_relat_1(sK5) = sK3 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_3546,c_48,c_54,c_55]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_15,plain,
% 3.76/0.98      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 3.76/0.98      | ~ v1_relat_1(X0)
% 3.76/0.98      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 3.76/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2539,plain,
% 3.76/0.98      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 3.76/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5025,plain,
% 3.76/0.98      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(sK3,X0) != iProver_top
% 3.76/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_3639,c_2539]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2982,plain,
% 3.76/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.76/0.98      | v1_relat_1(sK5) ),
% 3.76/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2983,plain,
% 3.76/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.76/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_2982]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5551,plain,
% 3.76/0.98      ( r1_xboole_0(sK3,X0) != iProver_top
% 3.76/0.98      | k7_relat_1(sK5,X0) = k1_xboole_0 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_5025,c_56,c_2983]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5552,plain,
% 3.76/0.98      ( k7_relat_1(sK5,X0) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(sK3,X0) != iProver_top ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_5551]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5559,plain,
% 3.76/0.98      ( k7_relat_1(sK5,sK4) = k1_xboole_0 ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2515,c_5552]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5,plain,
% 3.76/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.76/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2546,plain,
% 3.76/0.98      ( v1_relat_1(X0) != iProver_top
% 3.76/0.98      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5673,plain,
% 3.76/0.98      ( v1_relat_1(sK5) != iProver_top
% 3.76/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_5559,c_2546]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7516,plain,
% 3.76/0.98      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_5673,c_56,c_2983]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_6,plain,
% 3.76/0.98      ( ~ v1_relat_1(X0)
% 3.76/0.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.76/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2545,plain,
% 3.76/0.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.76/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7522,plain,
% 3.76/0.98      ( k9_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_7516,c_2545]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_11,plain,
% 3.76/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_12,plain,
% 3.76/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7524,plain,
% 3.76/0.98      ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.98      inference(light_normalisation,[status(thm)],[c_7522,c_11,c_12]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8020,plain,
% 3.76/0.98      ( k9_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.98      inference(light_normalisation,[status(thm)],[c_5813,c_7524]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8,plain,
% 3.76/0.98      ( r1_xboole_0(k1_relat_1(X0),X1)
% 3.76/0.98      | ~ v1_relat_1(X0)
% 3.76/0.98      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 3.76/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_2543,plain,
% 3.76/0.98      ( k9_relat_1(X0,X1) != k1_xboole_0
% 3.76/0.98      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 3.76/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.76/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8024,plain,
% 3.76/0.98      ( r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) = iProver_top
% 3.76/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_8020,c_2543]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8025,plain,
% 3.76/0.98      ( r1_xboole_0(sK4,k1_xboole_0) = iProver_top
% 3.76/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.98      inference(light_normalisation,[status(thm)],[c_8024,c_3663]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8028,plain,
% 3.76/0.98      ( r1_xboole_0(sK4,k1_xboole_0) = iProver_top ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_8025,c_59,c_2980]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5024,plain,
% 3.76/0.98      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(sK4,X0) != iProver_top
% 3.76/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_3663,c_2539]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5542,plain,
% 3.76/0.98      ( r1_xboole_0(sK4,X0) != iProver_top
% 3.76/0.98      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 3.76/0.98      inference(global_propositional_subsumption,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_5024,c_59,c_2980]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5543,plain,
% 3.76/0.98      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.98      | r1_xboole_0(sK4,X0) != iProver_top ),
% 3.76/0.98      inference(renaming,[status(thm)],[c_5542]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_8036,plain,
% 3.76/0.98      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_8028,c_5543]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13442,plain,
% 3.76/0.98      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.98      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 3.76/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.98      inference(light_normalisation,
% 3.76/0.98                [status(thm)],
% 3.76/0.98                [c_13441,c_3757,c_8036]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_13443,plain,
% 3.76/0.98      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.98      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
% 3.76/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.98      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.98      inference(demodulation,[status(thm)],[c_13442,c_4397]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_3717,plain,
% 3.76/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_2527,c_2537]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_4187,plain,
% 3.76/0.98      ( k9_relat_1(k7_relat_1(sK5,X0),k1_xboole_0) = k9_relat_1(sK5,k1_xboole_0) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_3717,c_2516]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_5674,plain,
% 3.76/0.98      ( k9_relat_1(sK5,k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_5559,c_4187]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7766,plain,
% 3.76/0.98      ( k9_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.98      inference(light_normalisation,[status(thm)],[c_5674,c_7524]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7770,plain,
% 3.76/0.98      ( r1_xboole_0(k1_relat_1(sK5),k1_xboole_0) = iProver_top
% 3.76/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.76/0.98      inference(superposition,[status(thm)],[c_7766,c_2543]) ).
% 3.76/0.98  
% 3.76/0.98  cnf(c_7771,plain,
% 3.76/0.98      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top
% 3.76/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.76/0.98      inference(light_normalisation,[status(thm)],[c_7770,c_3639]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7774,plain,
% 3.76/0.99      ( r1_xboole_0(sK3,k1_xboole_0) = iProver_top ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_7771,c_56,c_2983]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7781,plain,
% 3.76/0.99      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_7774,c_5552]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_13444,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.99      | k1_xboole_0 != k1_xboole_0
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(light_normalisation,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_13443,c_3757,c_7781]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_13445,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) = sK5
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_13444]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_28,plain,
% 3.76/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.76/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.76/0.99      | ~ v1_funct_1(X0)
% 3.76/0.99      | ~ v1_funct_1(X3)
% 3.76/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.76/0.99      | v1_xboole_0(X5)
% 3.76/0.99      | v1_xboole_0(X2)
% 3.76/0.99      | v1_xboole_0(X4)
% 3.76/0.99      | v1_xboole_0(X1)
% 3.76/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.76/0.99      inference(cnf_transformation,[],[f124]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_259,plain,
% 3.76/0.99      ( ~ v1_funct_1(X3)
% 3.76/0.99      | ~ v1_funct_1(X0)
% 3.76/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.76/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.99      | v1_xboole_0(X5)
% 3.76/0.99      | v1_xboole_0(X2)
% 3.76/0.99      | v1_xboole_0(X4)
% 3.76/0.99      | v1_xboole_0(X1)
% 3.76/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_28,c_32,c_31,c_30]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_260,plain,
% 3.76/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.76/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.76/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.76/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.76/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.76/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.76/0.99      | ~ v1_funct_1(X0)
% 3.76/0.99      | ~ v1_funct_1(X3)
% 3.76/0.99      | v1_xboole_0(X1)
% 3.76/0.99      | v1_xboole_0(X2)
% 3.76/0.99      | v1_xboole_0(X4)
% 3.76/0.99      | v1_xboole_0(X5)
% 3.76/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_259]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2517,plain,
% 3.76/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.76/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.76/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.76/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.76/0.99      | v1_funct_1(X2) != iProver_top
% 3.76/0.99      | v1_funct_1(X5) != iProver_top
% 3.76/0.99      | v1_xboole_0(X3) = iProver_top
% 3.76/0.99      | v1_xboole_0(X1) = iProver_top
% 3.76/0.99      | v1_xboole_0(X4) = iProver_top
% 3.76/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_260]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_2775,plain,
% 3.76/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 3.76/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.76/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.76/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.76/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.76/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.76/0.99      | v1_funct_1(X5) != iProver_top
% 3.76/0.99      | v1_funct_1(X2) != iProver_top
% 3.76/0.99      | v1_xboole_0(X0) = iProver_top
% 3.76/0.99      | v1_xboole_0(X1) = iProver_top
% 3.76/0.99      | v1_xboole_0(X4) = iProver_top ),
% 3.76/0.99      inference(forward_subsumption_resolution,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_2517,c_2547]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_8113,plain,
% 3.76/0.99      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 3.76/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.76/0.99      | v1_funct_2(sK5,sK3,sK2) != iProver_top
% 3.76/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.76/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.99      | v1_funct_1(X1) != iProver_top
% 3.76/0.99      | v1_funct_1(sK5) != iProver_top
% 3.76/0.99      | v1_xboole_0(X0) = iProver_top
% 3.76/0.99      | v1_xboole_0(sK2) = iProver_top
% 3.76/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_6921,c_2775]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10489,plain,
% 3.76/0.99      ( v1_funct_1(X1) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.76/0.99      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 3.76/0.99      | k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 3.76/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.76/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_8113,c_48,c_49,c_54,c_55,c_56]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10490,plain,
% 3.76/0.99      ( k2_partfun1(X0,sK2,X1,k9_subset_1(X2,sK3,X0)) != k7_relat_1(sK5,k9_subset_1(X2,sK3,X0))
% 3.76/0.99      | k2_partfun1(k4_subset_1(X2,sK3,X0),sK2,k1_tmap_1(X2,sK2,sK3,X0,sK5,X1),X0) = X1
% 3.76/0.99      | v1_funct_2(X1,X0,sK2) != iProver_top
% 3.76/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.76/0.99      | v1_funct_1(X1) != iProver_top
% 3.76/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.76/0.99      inference(renaming,[status(thm)],[c_10489]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10503,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 3.76/0.99      | v1_funct_2(sK6,sK4,sK2) != iProver_top
% 3.76/0.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK2))) != iProver_top
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.76/0.99      | v1_funct_1(sK6) != iProver_top
% 3.76/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_6915,c_10490]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10835,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(X0,sK3,sK4),sK2,k1_tmap_1(X0,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK3,sK4)) != k7_relat_1(sK6,k9_subset_1(X0,sK3,sK4))
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 3.76/0.99      inference(global_propositional_subsumption,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_10503,c_51,c_57,c_58,c_59]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10845,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | k7_relat_1(sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4))
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(superposition,[status(thm)],[c_4397,c_10835]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10846,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | k7_relat_1(sK5,k9_subset_1(sK1,sK3,sK4)) != k1_xboole_0
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(light_normalisation,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_10845,c_3757,c_8036]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10847,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,sK4))) != k1_xboole_0
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_10846,c_4397]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10848,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | k1_xboole_0 != k1_xboole_0
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(light_normalisation,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_10847,c_3757,c_7781]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_10849,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) = sK6
% 3.76/0.99      | m1_subset_1(sK4,k1_zfmisc_1(sK1)) != iProver_top
% 3.76/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top ),
% 3.76/0.99      inference(equality_resolution_simp,[status(thm)],[c_10848]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_33,negated_conjecture,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.76/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.76/0.99      | k2_partfun1(sK3,sK2,sK5,k9_subset_1(sK1,sK3,sK4)) != k2_partfun1(sK4,sK2,sK6,k9_subset_1(sK1,sK3,sK4)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_4571,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.76/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.76/0.99      | k2_partfun1(sK4,sK2,sK6,k1_setfam_1(k2_tarski(sK3,sK4))) != k2_partfun1(sK3,sK2,sK5,k1_setfam_1(k2_tarski(sK3,sK4))) ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_4397,c_33]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_4572,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.76/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.76/0.99      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k2_partfun1(sK4,sK2,sK6,k1_xboole_0) ),
% 3.76/0.99      inference(light_normalisation,[status(thm)],[c_4571,c_3757]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_6919,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.76/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.76/0.99      | k2_partfun1(sK3,sK2,sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_6915,c_4572]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7215,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.76/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.76/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK6,k1_xboole_0) ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_6919,c_6921]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_7889,plain,
% 3.76/0.99      ( k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK4) != sK6
% 3.76/0.99      | k2_partfun1(k4_subset_1(sK1,sK3,sK4),sK2,k1_tmap_1(sK1,sK2,sK3,sK4,sK5,sK6),sK3) != sK5
% 3.76/0.99      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.76/0.99      inference(demodulation,[status(thm)],[c_7781,c_7215]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1593,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_6020,plain,
% 3.76/0.99      ( k9_relat_1(X0,X1) != X2
% 3.76/0.99      | k1_xboole_0 != X2
% 3.76/0.99      | k1_xboole_0 = k9_relat_1(X0,X1) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1593]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_6021,plain,
% 3.76/0.99      ( k9_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.76/0.99      | k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
% 3.76/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_6020]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3705,plain,
% 3.76/0.99      ( k9_relat_1(sK6,X0) != X1
% 3.76/0.99      | k9_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.99      | k1_xboole_0 != X1 ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1593]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5760,plain,
% 3.76/0.99      ( k9_relat_1(sK6,X0) != k9_relat_1(X1,X2)
% 3.76/0.99      | k9_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.99      | k1_xboole_0 != k9_relat_1(X1,X2) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_3705]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_5762,plain,
% 3.76/0.99      ( k9_relat_1(sK6,k1_xboole_0) != k9_relat_1(k1_xboole_0,k1_xboole_0)
% 3.76/0.99      | k9_relat_1(sK6,k1_xboole_0) = k1_xboole_0
% 3.76/0.99      | k1_xboole_0 != k9_relat_1(k1_xboole_0,k1_xboole_0) ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_5760]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3164,plain,
% 3.76/0.99      ( ~ r1_xboole_0(k1_relat_1(sK6),X0)
% 3.76/0.99      | ~ v1_relat_1(sK6)
% 3.76/0.99      | k7_relat_1(sK6,X0) = k1_xboole_0 ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3199,plain,
% 3.76/0.99      ( k7_relat_1(sK6,X0) = k1_xboole_0
% 3.76/0.99      | r1_xboole_0(k1_relat_1(sK6),X0) != iProver_top
% 3.76/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_3164]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3201,plain,
% 3.76/0.99      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0
% 3.76/0.99      | r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) != iProver_top
% 3.76/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_3199]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3165,plain,
% 3.76/0.99      ( r1_xboole_0(k1_relat_1(sK6),X0)
% 3.76/0.99      | ~ v1_relat_1(sK6)
% 3.76/0.99      | k9_relat_1(sK6,X0) != k1_xboole_0 ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3195,plain,
% 3.76/0.99      ( k9_relat_1(sK6,X0) != k1_xboole_0
% 3.76/0.99      | r1_xboole_0(k1_relat_1(sK6),X0) = iProver_top
% 3.76/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_3165]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_3197,plain,
% 3.76/0.99      ( k9_relat_1(sK6,k1_xboole_0) != k1_xboole_0
% 3.76/0.99      | r1_xboole_0(k1_relat_1(sK6),k1_xboole_0) = iProver_top
% 3.76/0.99      | v1_relat_1(sK6) != iProver_top ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_3195]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1592,plain,( X0 = X0 ),theory(equality) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_1627,plain,
% 3.76/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.76/0.99      inference(instantiation,[status(thm)],[c_1592]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_52,plain,
% 3.76/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_43,negated_conjecture,
% 3.76/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 3.76/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(c_50,plain,
% 3.76/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.76/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.76/0.99  
% 3.76/0.99  cnf(contradiction,plain,
% 3.76/0.99      ( $false ),
% 3.76/0.99      inference(minisat,
% 3.76/0.99                [status(thm)],
% 3.76/0.99                [c_13445,c_10849,c_7889,c_7524,c_6021,c_5813,c_5762,
% 3.76/0.99                 c_3201,c_3197,c_2980,c_1627,c_59,c_52,c_50]) ).
% 3.76/0.99  
% 3.76/0.99  
% 3.76/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.76/0.99  
% 3.76/0.99  ------                               Statistics
% 3.76/0.99  
% 3.76/0.99  ------ Selected
% 3.76/0.99  
% 3.76/0.99  total_time:                             0.425
% 3.76/0.99  
%------------------------------------------------------------------------------
