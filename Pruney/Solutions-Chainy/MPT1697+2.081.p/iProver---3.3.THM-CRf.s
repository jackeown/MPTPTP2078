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
% DateTime   : Thu Dec  3 12:21:41 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  243 (4118 expanded)
%              Number of clauses        :  169 (1161 expanded)
%              Number of leaves         :   19 (1557 expanded)
%              Depth                    :   25
%              Number of atoms          : 1354 (51127 expanded)
%              Number of equality atoms :  630 (12195 expanded)
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

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f42,f41,f40,f39,f38,f37])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f66,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f27,plain,(
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
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
    inference(equality_resolution,[],[f56])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
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
    inference(equality_resolution,[],[f57])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_704,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1207,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_690,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_relat_1(X0_51)
    | k7_relat_1(X0_51,X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_1221,plain,
    ( k7_relat_1(X0_51,X1_51) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_3494,plain,
    ( k7_relat_1(sK5,sK3) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1221])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_712,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1541,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X1_51,X2_51)) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1712,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_1713,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_711,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1752,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1753,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1752])).

cnf(c_3539,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3494,c_44,c_1713,c_1753])).

cnf(c_1200,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_2405,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1200])).

cnf(c_2928,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2405,c_44,c_1713,c_1753])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_463,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_2])).

cnf(c_464,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_463])).

cnf(c_688,plain,
    ( ~ v1_relat_1(X0_51)
    | k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_464])).

cnf(c_1223,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_2933,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0_51),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2928,c_1223])).

cnf(c_4048,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3539,c_2933])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_698,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1213,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_713,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1199,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_2387,plain,
    ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1213,c_1199])).

cnf(c_18,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_705,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_2753,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2387,c_705])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_235,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_435,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_436,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_438,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_29,c_27])).

cnf(c_493,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_235,c_438])).

cnf(c_494,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_685,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_2754,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2753,c_685])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1202,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2481,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1202])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1617,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1773,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_1617])).

cnf(c_3295,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2481,c_21,c_19,c_1773])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_701,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1210,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_2482,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1202])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1778,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3372,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2482,c_24,c_22,c_1778])).

cnf(c_4017,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2754,c_3295,c_3372])).

cnf(c_4050,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4048,c_4017])).

cnf(c_3495,plain,
    ( k7_relat_1(sK4,sK2) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1221])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1715,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1541])).

cnf(c_1716,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1715])).

cnf(c_1755,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_1756,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1755])).

cnf(c_4014,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3495,c_41,c_1716,c_1756])).

cnf(c_2406,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1200])).

cnf(c_2941,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2406,c_41,c_1716,c_1756])).

cnf(c_2946,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0_51),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2941,c_1223])).

cnf(c_4106,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4014,c_2946])).

cnf(c_16343,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4050,c_4106])).

cnf(c_16344,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_16343])).

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
    inference(cnf_transformation,[],[f61])).

cnf(c_708,plain,
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

cnf(c_1204,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_2618,plain,
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
    inference(superposition,[status(thm)],[c_1204,c_1202])).

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
    inference(cnf_transformation,[],[f59])).

cnf(c_706,plain,
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

cnf(c_1206,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_7634,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_2618,c_1206])).

cnf(c_7638,plain,
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
    inference(superposition,[status(thm)],[c_1207,c_7634])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_33,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_36,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7952,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7638,c_33,c_36,c_42,c_43])).

cnf(c_7953,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_7952])).

cnf(c_7967,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_7953])).

cnf(c_34,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8323,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7967,c_34,c_39,c_40])).

cnf(c_8324,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_8323])).

cnf(c_8333,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_8324])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_32,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8365,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8333,c_32,c_35])).

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
    inference(cnf_transformation,[],[f79])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_174,plain,
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

cnf(c_175,plain,
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
    inference(renaming,[status(thm)],[c_174])).

cnf(c_692,plain,
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
    inference(subtyping,[status(esa)],[c_175])).

cnf(c_1219,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_4184,plain,
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
    inference(superposition,[status(thm)],[c_3295,c_1219])).

cnf(c_10436,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4184,c_33,c_36,c_42,c_43,c_44])).

cnf(c_10437,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_10436])).

cnf(c_10457,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_10437])).

cnf(c_10467,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10457,c_2387])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11073,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10467,c_32,c_37])).

cnf(c_11074,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_11073])).

cnf(c_11087,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_11074])).

cnf(c_11171,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11087,c_685,c_4048,c_4106])).

cnf(c_11172,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11171])).

cnf(c_11173,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11172,c_8365])).

cnf(c_10452,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_10437])).

cnf(c_11055,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10452,c_34,c_39,c_40,c_41])).

cnf(c_11056,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_11055])).

cnf(c_11066,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_11056])).

cnf(c_11067,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11066,c_685,c_4048])).

cnf(c_11068,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11067,c_2387,c_8365])).

cnf(c_11069,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11068,c_685,c_4106])).

cnf(c_11070,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11069])).

cnf(c_11255,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11173,c_32,c_35,c_37,c_11070])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_181,plain,
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

cnf(c_182,plain,
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
    inference(renaming,[status(thm)],[c_181])).

cnf(c_691,plain,
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
    inference(subtyping,[status(esa)],[c_182])).

cnf(c_1220,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_5811,plain,
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
    inference(superposition,[status(thm)],[c_3295,c_1220])).

cnf(c_14191,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5811,c_33,c_36,c_42,c_43,c_44])).

cnf(c_14192,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_14191])).

cnf(c_14212,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_14192])).

cnf(c_14222,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14212,c_2387])).

cnf(c_14409,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14222,c_32,c_37])).

cnf(c_14410,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_14409])).

cnf(c_14423,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_14410])).

cnf(c_14507,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14423,c_685,c_4048,c_4106])).

cnf(c_14508,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14507])).

cnf(c_14509,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14508,c_8365])).

cnf(c_14207,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_14192])).

cnf(c_14341,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14207,c_34,c_39,c_40,c_41])).

cnf(c_14342,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_14341])).

cnf(c_14352,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_14342])).

cnf(c_14353,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14352,c_685,c_4048])).

cnf(c_14354,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14353,c_2387,c_8365])).

cnf(c_14355,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14354,c_685,c_4106])).

cnf(c_14356,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14355])).

cnf(c_14525,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14509,c_32,c_35,c_37,c_14356])).

cnf(c_16345,plain,
    ( sK5 != sK5
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_16344,c_8365,c_11255,c_14525])).

cnf(c_16346,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16345])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 7.56/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.49  
% 7.56/1.49  ------  iProver source info
% 7.56/1.49  
% 7.56/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.49  git: non_committed_changes: false
% 7.56/1.49  git: last_make_outside_of_git: false
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  
% 7.56/1.49  ------ Input Options
% 7.56/1.49  
% 7.56/1.49  --out_options                           all
% 7.56/1.49  --tptp_safe_out                         true
% 7.56/1.49  --problem_path                          ""
% 7.56/1.49  --include_path                          ""
% 7.56/1.49  --clausifier                            res/vclausify_rel
% 7.56/1.49  --clausifier_options                    --mode clausify
% 7.56/1.49  --stdin                                 false
% 7.56/1.49  --stats_out                             all
% 7.56/1.49  
% 7.56/1.49  ------ General Options
% 7.56/1.49  
% 7.56/1.49  --fof                                   false
% 7.56/1.49  --time_out_real                         305.
% 7.56/1.49  --time_out_virtual                      -1.
% 7.56/1.49  --symbol_type_check                     false
% 7.56/1.49  --clausify_out                          false
% 7.56/1.49  --sig_cnt_out                           false
% 7.56/1.49  --trig_cnt_out                          false
% 7.56/1.49  --trig_cnt_out_tolerance                1.
% 7.56/1.49  --trig_cnt_out_sk_spl                   false
% 7.56/1.49  --abstr_cl_out                          false
% 7.56/1.49  
% 7.56/1.49  ------ Global Options
% 7.56/1.49  
% 7.56/1.49  --schedule                              default
% 7.56/1.49  --add_important_lit                     false
% 7.56/1.49  --prop_solver_per_cl                    1000
% 7.56/1.49  --min_unsat_core                        false
% 7.56/1.49  --soft_assumptions                      false
% 7.56/1.49  --soft_lemma_size                       3
% 7.56/1.49  --prop_impl_unit_size                   0
% 7.56/1.49  --prop_impl_unit                        []
% 7.56/1.49  --share_sel_clauses                     true
% 7.56/1.49  --reset_solvers                         false
% 7.56/1.49  --bc_imp_inh                            [conj_cone]
% 7.56/1.49  --conj_cone_tolerance                   3.
% 7.56/1.49  --extra_neg_conj                        none
% 7.56/1.49  --large_theory_mode                     true
% 7.56/1.49  --prolific_symb_bound                   200
% 7.56/1.49  --lt_threshold                          2000
% 7.56/1.49  --clause_weak_htbl                      true
% 7.56/1.49  --gc_record_bc_elim                     false
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing Options
% 7.56/1.49  
% 7.56/1.49  --preprocessing_flag                    true
% 7.56/1.49  --time_out_prep_mult                    0.1
% 7.56/1.49  --splitting_mode                        input
% 7.56/1.49  --splitting_grd                         true
% 7.56/1.49  --splitting_cvd                         false
% 7.56/1.49  --splitting_cvd_svl                     false
% 7.56/1.49  --splitting_nvd                         32
% 7.56/1.49  --sub_typing                            true
% 7.56/1.49  --prep_gs_sim                           true
% 7.56/1.49  --prep_unflatten                        true
% 7.56/1.49  --prep_res_sim                          true
% 7.56/1.49  --prep_upred                            true
% 7.56/1.49  --prep_sem_filter                       exhaustive
% 7.56/1.49  --prep_sem_filter_out                   false
% 7.56/1.49  --pred_elim                             true
% 7.56/1.49  --res_sim_input                         true
% 7.56/1.49  --eq_ax_congr_red                       true
% 7.56/1.49  --pure_diseq_elim                       true
% 7.56/1.49  --brand_transform                       false
% 7.56/1.49  --non_eq_to_eq                          false
% 7.56/1.49  --prep_def_merge                        true
% 7.56/1.49  --prep_def_merge_prop_impl              false
% 7.56/1.49  --prep_def_merge_mbd                    true
% 7.56/1.49  --prep_def_merge_tr_red                 false
% 7.56/1.49  --prep_def_merge_tr_cl                  false
% 7.56/1.49  --smt_preprocessing                     true
% 7.56/1.49  --smt_ac_axioms                         fast
% 7.56/1.49  --preprocessed_out                      false
% 7.56/1.49  --preprocessed_stats                    false
% 7.56/1.49  
% 7.56/1.49  ------ Abstraction refinement Options
% 7.56/1.49  
% 7.56/1.49  --abstr_ref                             []
% 7.56/1.49  --abstr_ref_prep                        false
% 7.56/1.49  --abstr_ref_until_sat                   false
% 7.56/1.49  --abstr_ref_sig_restrict                funpre
% 7.56/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.56/1.49  --abstr_ref_under                       []
% 7.56/1.49  
% 7.56/1.49  ------ SAT Options
% 7.56/1.49  
% 7.56/1.49  --sat_mode                              false
% 7.56/1.49  --sat_fm_restart_options                ""
% 7.56/1.49  --sat_gr_def                            false
% 7.56/1.49  --sat_epr_types                         true
% 7.56/1.49  --sat_non_cyclic_types                  false
% 7.56/1.49  --sat_finite_models                     false
% 7.56/1.49  --sat_fm_lemmas                         false
% 7.56/1.49  --sat_fm_prep                           false
% 7.56/1.49  --sat_fm_uc_incr                        true
% 7.56/1.49  --sat_out_model                         small
% 7.56/1.49  --sat_out_clauses                       false
% 7.56/1.49  
% 7.56/1.49  ------ QBF Options
% 7.56/1.49  
% 7.56/1.49  --qbf_mode                              false
% 7.56/1.49  --qbf_elim_univ                         false
% 7.56/1.49  --qbf_dom_inst                          none
% 7.56/1.49  --qbf_dom_pre_inst                      false
% 7.56/1.49  --qbf_sk_in                             false
% 7.56/1.49  --qbf_pred_elim                         true
% 7.56/1.49  --qbf_split                             512
% 7.56/1.49  
% 7.56/1.49  ------ BMC1 Options
% 7.56/1.49  
% 7.56/1.49  --bmc1_incremental                      false
% 7.56/1.49  --bmc1_axioms                           reachable_all
% 7.56/1.49  --bmc1_min_bound                        0
% 7.56/1.49  --bmc1_max_bound                        -1
% 7.56/1.49  --bmc1_max_bound_default                -1
% 7.56/1.49  --bmc1_symbol_reachability              true
% 7.56/1.49  --bmc1_property_lemmas                  false
% 7.56/1.49  --bmc1_k_induction                      false
% 7.56/1.49  --bmc1_non_equiv_states                 false
% 7.56/1.49  --bmc1_deadlock                         false
% 7.56/1.49  --bmc1_ucm                              false
% 7.56/1.49  --bmc1_add_unsat_core                   none
% 7.56/1.49  --bmc1_unsat_core_children              false
% 7.56/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.56/1.49  --bmc1_out_stat                         full
% 7.56/1.49  --bmc1_ground_init                      false
% 7.56/1.49  --bmc1_pre_inst_next_state              false
% 7.56/1.49  --bmc1_pre_inst_state                   false
% 7.56/1.49  --bmc1_pre_inst_reach_state             false
% 7.56/1.49  --bmc1_out_unsat_core                   false
% 7.56/1.49  --bmc1_aig_witness_out                  false
% 7.56/1.49  --bmc1_verbose                          false
% 7.56/1.49  --bmc1_dump_clauses_tptp                false
% 7.56/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.56/1.49  --bmc1_dump_file                        -
% 7.56/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.56/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.56/1.49  --bmc1_ucm_extend_mode                  1
% 7.56/1.49  --bmc1_ucm_init_mode                    2
% 7.56/1.49  --bmc1_ucm_cone_mode                    none
% 7.56/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.56/1.49  --bmc1_ucm_relax_model                  4
% 7.56/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.56/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.56/1.49  --bmc1_ucm_layered_model                none
% 7.56/1.49  --bmc1_ucm_max_lemma_size               10
% 7.56/1.49  
% 7.56/1.49  ------ AIG Options
% 7.56/1.49  
% 7.56/1.49  --aig_mode                              false
% 7.56/1.49  
% 7.56/1.49  ------ Instantiation Options
% 7.56/1.49  
% 7.56/1.49  --instantiation_flag                    true
% 7.56/1.49  --inst_sos_flag                         false
% 7.56/1.49  --inst_sos_phase                        true
% 7.56/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.56/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.56/1.49  --inst_lit_sel_side                     num_symb
% 7.56/1.49  --inst_solver_per_active                1400
% 7.56/1.49  --inst_solver_calls_frac                1.
% 7.56/1.49  --inst_passive_queue_type               priority_queues
% 7.56/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.56/1.49  --inst_passive_queues_freq              [25;2]
% 7.56/1.49  --inst_dismatching                      true
% 7.56/1.49  --inst_eager_unprocessed_to_passive     true
% 7.56/1.49  --inst_prop_sim_given                   true
% 7.56/1.49  --inst_prop_sim_new                     false
% 7.56/1.49  --inst_subs_new                         false
% 7.56/1.49  --inst_eq_res_simp                      false
% 7.56/1.49  --inst_subs_given                       false
% 7.56/1.49  --inst_orphan_elimination               true
% 7.56/1.49  --inst_learning_loop_flag               true
% 7.56/1.49  --inst_learning_start                   3000
% 7.56/1.49  --inst_learning_factor                  2
% 7.56/1.49  --inst_start_prop_sim_after_learn       3
% 7.56/1.49  --inst_sel_renew                        solver
% 7.56/1.49  --inst_lit_activity_flag                true
% 7.56/1.49  --inst_restr_to_given                   false
% 7.56/1.49  --inst_activity_threshold               500
% 7.56/1.49  --inst_out_proof                        true
% 7.56/1.49  
% 7.56/1.49  ------ Resolution Options
% 7.56/1.49  
% 7.56/1.49  --resolution_flag                       true
% 7.56/1.49  --res_lit_sel                           adaptive
% 7.56/1.49  --res_lit_sel_side                      none
% 7.56/1.49  --res_ordering                          kbo
% 7.56/1.49  --res_to_prop_solver                    active
% 7.56/1.49  --res_prop_simpl_new                    false
% 7.56/1.49  --res_prop_simpl_given                  true
% 7.56/1.49  --res_passive_queue_type                priority_queues
% 7.56/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.56/1.49  --res_passive_queues_freq               [15;5]
% 7.56/1.49  --res_forward_subs                      full
% 7.56/1.49  --res_backward_subs                     full
% 7.56/1.49  --res_forward_subs_resolution           true
% 7.56/1.49  --res_backward_subs_resolution          true
% 7.56/1.49  --res_orphan_elimination                true
% 7.56/1.49  --res_time_limit                        2.
% 7.56/1.49  --res_out_proof                         true
% 7.56/1.49  
% 7.56/1.49  ------ Superposition Options
% 7.56/1.49  
% 7.56/1.49  --superposition_flag                    true
% 7.56/1.49  --sup_passive_queue_type                priority_queues
% 7.56/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.56/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.56/1.49  --demod_completeness_check              fast
% 7.56/1.49  --demod_use_ground                      true
% 7.56/1.49  --sup_to_prop_solver                    passive
% 7.56/1.49  --sup_prop_simpl_new                    true
% 7.56/1.49  --sup_prop_simpl_given                  true
% 7.56/1.49  --sup_fun_splitting                     false
% 7.56/1.49  --sup_smt_interval                      50000
% 7.56/1.49  
% 7.56/1.49  ------ Superposition Simplification Setup
% 7.56/1.49  
% 7.56/1.49  --sup_indices_passive                   []
% 7.56/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.56/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.49  --sup_full_bw                           [BwDemod]
% 7.56/1.49  --sup_immed_triv                        [TrivRules]
% 7.56/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.49  --sup_immed_bw_main                     []
% 7.56/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.56/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.49  
% 7.56/1.49  ------ Combination Options
% 7.56/1.49  
% 7.56/1.49  --comb_res_mult                         3
% 7.56/1.49  --comb_sup_mult                         2
% 7.56/1.49  --comb_inst_mult                        10
% 7.56/1.49  
% 7.56/1.49  ------ Debug Options
% 7.56/1.49  
% 7.56/1.49  --dbg_backtrace                         false
% 7.56/1.49  --dbg_dump_prop_clauses                 false
% 7.56/1.49  --dbg_dump_prop_clauses_file            -
% 7.56/1.49  --dbg_out_stat                          false
% 7.56/1.49  ------ Parsing...
% 7.56/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.49  ------ Proving...
% 7.56/1.49  ------ Problem Properties 
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  clauses                                 29
% 7.56/1.49  conjectures                             13
% 7.56/1.49  EPR                                     8
% 7.56/1.49  Horn                                    23
% 7.56/1.49  unary                                   15
% 7.56/1.49  binary                                  3
% 7.56/1.49  lits                                    120
% 7.56/1.49  lits eq                                 18
% 7.56/1.49  fd_pure                                 0
% 7.56/1.49  fd_pseudo                               0
% 7.56/1.49  fd_cond                                 0
% 7.56/1.49  fd_pseudo_cond                          0
% 7.56/1.49  AC symbols                              0
% 7.56/1.49  
% 7.56/1.49  ------ Schedule dynamic 5 is on 
% 7.56/1.49  
% 7.56/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ 
% 7.56/1.49  Current options:
% 7.56/1.49  ------ 
% 7.56/1.49  
% 7.56/1.49  ------ Input Options
% 7.56/1.49  
% 7.56/1.49  --out_options                           all
% 7.56/1.49  --tptp_safe_out                         true
% 7.56/1.49  --problem_path                          ""
% 7.56/1.49  --include_path                          ""
% 7.56/1.49  --clausifier                            res/vclausify_rel
% 7.56/1.49  --clausifier_options                    --mode clausify
% 7.56/1.49  --stdin                                 false
% 7.56/1.49  --stats_out                             all
% 7.56/1.49  
% 7.56/1.49  ------ General Options
% 7.56/1.49  
% 7.56/1.49  --fof                                   false
% 7.56/1.49  --time_out_real                         305.
% 7.56/1.49  --time_out_virtual                      -1.
% 7.56/1.49  --symbol_type_check                     false
% 7.56/1.49  --clausify_out                          false
% 7.56/1.49  --sig_cnt_out                           false
% 7.56/1.49  --trig_cnt_out                          false
% 7.56/1.49  --trig_cnt_out_tolerance                1.
% 7.56/1.49  --trig_cnt_out_sk_spl                   false
% 7.56/1.49  --abstr_cl_out                          false
% 7.56/1.49  
% 7.56/1.49  ------ Global Options
% 7.56/1.49  
% 7.56/1.49  --schedule                              default
% 7.56/1.49  --add_important_lit                     false
% 7.56/1.49  --prop_solver_per_cl                    1000
% 7.56/1.49  --min_unsat_core                        false
% 7.56/1.49  --soft_assumptions                      false
% 7.56/1.49  --soft_lemma_size                       3
% 7.56/1.49  --prop_impl_unit_size                   0
% 7.56/1.49  --prop_impl_unit                        []
% 7.56/1.49  --share_sel_clauses                     true
% 7.56/1.49  --reset_solvers                         false
% 7.56/1.49  --bc_imp_inh                            [conj_cone]
% 7.56/1.49  --conj_cone_tolerance                   3.
% 7.56/1.49  --extra_neg_conj                        none
% 7.56/1.49  --large_theory_mode                     true
% 7.56/1.49  --prolific_symb_bound                   200
% 7.56/1.49  --lt_threshold                          2000
% 7.56/1.49  --clause_weak_htbl                      true
% 7.56/1.49  --gc_record_bc_elim                     false
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing Options
% 7.56/1.49  
% 7.56/1.49  --preprocessing_flag                    true
% 7.56/1.49  --time_out_prep_mult                    0.1
% 7.56/1.49  --splitting_mode                        input
% 7.56/1.49  --splitting_grd                         true
% 7.56/1.49  --splitting_cvd                         false
% 7.56/1.49  --splitting_cvd_svl                     false
% 7.56/1.49  --splitting_nvd                         32
% 7.56/1.49  --sub_typing                            true
% 7.56/1.49  --prep_gs_sim                           true
% 7.56/1.49  --prep_unflatten                        true
% 7.56/1.49  --prep_res_sim                          true
% 7.56/1.49  --prep_upred                            true
% 7.56/1.49  --prep_sem_filter                       exhaustive
% 7.56/1.49  --prep_sem_filter_out                   false
% 7.56/1.49  --pred_elim                             true
% 7.56/1.49  --res_sim_input                         true
% 7.56/1.49  --eq_ax_congr_red                       true
% 7.56/1.49  --pure_diseq_elim                       true
% 7.56/1.49  --brand_transform                       false
% 7.56/1.49  --non_eq_to_eq                          false
% 7.56/1.49  --prep_def_merge                        true
% 7.56/1.49  --prep_def_merge_prop_impl              false
% 7.56/1.49  --prep_def_merge_mbd                    true
% 7.56/1.49  --prep_def_merge_tr_red                 false
% 7.56/1.49  --prep_def_merge_tr_cl                  false
% 7.56/1.49  --smt_preprocessing                     true
% 7.56/1.49  --smt_ac_axioms                         fast
% 7.56/1.49  --preprocessed_out                      false
% 7.56/1.49  --preprocessed_stats                    false
% 7.56/1.49  
% 7.56/1.49  ------ Abstraction refinement Options
% 7.56/1.49  
% 7.56/1.49  --abstr_ref                             []
% 7.56/1.49  --abstr_ref_prep                        false
% 7.56/1.49  --abstr_ref_until_sat                   false
% 7.56/1.49  --abstr_ref_sig_restrict                funpre
% 7.56/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.56/1.49  --abstr_ref_under                       []
% 7.56/1.49  
% 7.56/1.49  ------ SAT Options
% 7.56/1.49  
% 7.56/1.49  --sat_mode                              false
% 7.56/1.49  --sat_fm_restart_options                ""
% 7.56/1.49  --sat_gr_def                            false
% 7.56/1.49  --sat_epr_types                         true
% 7.56/1.49  --sat_non_cyclic_types                  false
% 7.56/1.49  --sat_finite_models                     false
% 7.56/1.49  --sat_fm_lemmas                         false
% 7.56/1.49  --sat_fm_prep                           false
% 7.56/1.49  --sat_fm_uc_incr                        true
% 7.56/1.49  --sat_out_model                         small
% 7.56/1.49  --sat_out_clauses                       false
% 7.56/1.49  
% 7.56/1.49  ------ QBF Options
% 7.56/1.49  
% 7.56/1.49  --qbf_mode                              false
% 7.56/1.49  --qbf_elim_univ                         false
% 7.56/1.49  --qbf_dom_inst                          none
% 7.56/1.49  --qbf_dom_pre_inst                      false
% 7.56/1.49  --qbf_sk_in                             false
% 7.56/1.49  --qbf_pred_elim                         true
% 7.56/1.49  --qbf_split                             512
% 7.56/1.49  
% 7.56/1.49  ------ BMC1 Options
% 7.56/1.49  
% 7.56/1.49  --bmc1_incremental                      false
% 7.56/1.49  --bmc1_axioms                           reachable_all
% 7.56/1.49  --bmc1_min_bound                        0
% 7.56/1.49  --bmc1_max_bound                        -1
% 7.56/1.49  --bmc1_max_bound_default                -1
% 7.56/1.49  --bmc1_symbol_reachability              true
% 7.56/1.49  --bmc1_property_lemmas                  false
% 7.56/1.49  --bmc1_k_induction                      false
% 7.56/1.49  --bmc1_non_equiv_states                 false
% 7.56/1.49  --bmc1_deadlock                         false
% 7.56/1.49  --bmc1_ucm                              false
% 7.56/1.49  --bmc1_add_unsat_core                   none
% 7.56/1.49  --bmc1_unsat_core_children              false
% 7.56/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.56/1.49  --bmc1_out_stat                         full
% 7.56/1.49  --bmc1_ground_init                      false
% 7.56/1.49  --bmc1_pre_inst_next_state              false
% 7.56/1.49  --bmc1_pre_inst_state                   false
% 7.56/1.49  --bmc1_pre_inst_reach_state             false
% 7.56/1.49  --bmc1_out_unsat_core                   false
% 7.56/1.49  --bmc1_aig_witness_out                  false
% 7.56/1.49  --bmc1_verbose                          false
% 7.56/1.49  --bmc1_dump_clauses_tptp                false
% 7.56/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.56/1.49  --bmc1_dump_file                        -
% 7.56/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.56/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.56/1.49  --bmc1_ucm_extend_mode                  1
% 7.56/1.49  --bmc1_ucm_init_mode                    2
% 7.56/1.49  --bmc1_ucm_cone_mode                    none
% 7.56/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.56/1.49  --bmc1_ucm_relax_model                  4
% 7.56/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.56/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.56/1.49  --bmc1_ucm_layered_model                none
% 7.56/1.49  --bmc1_ucm_max_lemma_size               10
% 7.56/1.49  
% 7.56/1.49  ------ AIG Options
% 7.56/1.49  
% 7.56/1.49  --aig_mode                              false
% 7.56/1.49  
% 7.56/1.49  ------ Instantiation Options
% 7.56/1.49  
% 7.56/1.49  --instantiation_flag                    true
% 7.56/1.49  --inst_sos_flag                         false
% 7.56/1.49  --inst_sos_phase                        true
% 7.56/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.56/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.56/1.49  --inst_lit_sel_side                     none
% 7.56/1.49  --inst_solver_per_active                1400
% 7.56/1.49  --inst_solver_calls_frac                1.
% 7.56/1.49  --inst_passive_queue_type               priority_queues
% 7.56/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.56/1.49  --inst_passive_queues_freq              [25;2]
% 7.56/1.49  --inst_dismatching                      true
% 7.56/1.49  --inst_eager_unprocessed_to_passive     true
% 7.56/1.49  --inst_prop_sim_given                   true
% 7.56/1.49  --inst_prop_sim_new                     false
% 7.56/1.49  --inst_subs_new                         false
% 7.56/1.49  --inst_eq_res_simp                      false
% 7.56/1.49  --inst_subs_given                       false
% 7.56/1.49  --inst_orphan_elimination               true
% 7.56/1.49  --inst_learning_loop_flag               true
% 7.56/1.49  --inst_learning_start                   3000
% 7.56/1.49  --inst_learning_factor                  2
% 7.56/1.49  --inst_start_prop_sim_after_learn       3
% 7.56/1.49  --inst_sel_renew                        solver
% 7.56/1.49  --inst_lit_activity_flag                true
% 7.56/1.49  --inst_restr_to_given                   false
% 7.56/1.49  --inst_activity_threshold               500
% 7.56/1.49  --inst_out_proof                        true
% 7.56/1.49  
% 7.56/1.49  ------ Resolution Options
% 7.56/1.49  
% 7.56/1.49  --resolution_flag                       false
% 7.56/1.49  --res_lit_sel                           adaptive
% 7.56/1.49  --res_lit_sel_side                      none
% 7.56/1.49  --res_ordering                          kbo
% 7.56/1.49  --res_to_prop_solver                    active
% 7.56/1.49  --res_prop_simpl_new                    false
% 7.56/1.49  --res_prop_simpl_given                  true
% 7.56/1.49  --res_passive_queue_type                priority_queues
% 7.56/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.56/1.49  --res_passive_queues_freq               [15;5]
% 7.56/1.49  --res_forward_subs                      full
% 7.56/1.49  --res_backward_subs                     full
% 7.56/1.49  --res_forward_subs_resolution           true
% 7.56/1.49  --res_backward_subs_resolution          true
% 7.56/1.49  --res_orphan_elimination                true
% 7.56/1.49  --res_time_limit                        2.
% 7.56/1.49  --res_out_proof                         true
% 7.56/1.49  
% 7.56/1.49  ------ Superposition Options
% 7.56/1.49  
% 7.56/1.49  --superposition_flag                    true
% 7.56/1.49  --sup_passive_queue_type                priority_queues
% 7.56/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.56/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.56/1.49  --demod_completeness_check              fast
% 7.56/1.49  --demod_use_ground                      true
% 7.56/1.49  --sup_to_prop_solver                    passive
% 7.56/1.49  --sup_prop_simpl_new                    true
% 7.56/1.49  --sup_prop_simpl_given                  true
% 7.56/1.49  --sup_fun_splitting                     false
% 7.56/1.49  --sup_smt_interval                      50000
% 7.56/1.49  
% 7.56/1.49  ------ Superposition Simplification Setup
% 7.56/1.49  
% 7.56/1.49  --sup_indices_passive                   []
% 7.56/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.56/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.56/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.49  --sup_full_bw                           [BwDemod]
% 7.56/1.49  --sup_immed_triv                        [TrivRules]
% 7.56/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.56/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.49  --sup_immed_bw_main                     []
% 7.56/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.56/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.56/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.56/1.49  
% 7.56/1.49  ------ Combination Options
% 7.56/1.49  
% 7.56/1.49  --comb_res_mult                         3
% 7.56/1.49  --comb_sup_mult                         2
% 7.56/1.49  --comb_inst_mult                        10
% 7.56/1.49  
% 7.56/1.49  ------ Debug Options
% 7.56/1.49  
% 7.56/1.49  --dbg_backtrace                         false
% 7.56/1.49  --dbg_dump_prop_clauses                 false
% 7.56/1.49  --dbg_dump_prop_clauses_file            -
% 7.56/1.49  --dbg_out_stat                          false
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  ------ Proving...
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS status Theorem for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49   Resolution empty clause
% 7.56/1.49  
% 7.56/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  fof(f13,conjecture,(
% 7.56/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f14,negated_conjecture,(
% 7.56/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.56/1.49    inference(negated_conjecture,[],[f13])).
% 7.56/1.49  
% 7.56/1.49  fof(f31,plain,(
% 7.56/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.56/1.49    inference(ennf_transformation,[],[f14])).
% 7.56/1.49  
% 7.56/1.49  fof(f32,plain,(
% 7.56/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.56/1.49    inference(flattening,[],[f31])).
% 7.56/1.49  
% 7.56/1.49  fof(f42,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f41,plain,(
% 7.56/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f40,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f39,plain,(
% 7.56/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f38,plain,(
% 7.56/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f37,plain,(
% 7.56/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.56/1.49    introduced(choice_axiom,[])).
% 7.56/1.49  
% 7.56/1.49  fof(f43,plain,(
% 7.56/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.56/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f42,f41,f40,f39,f38,f37])).
% 7.56/1.49  
% 7.56/1.49  fof(f74,plain,(
% 7.56/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f9,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f15,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.56/1.49    inference(pure_predicate_removal,[],[f9])).
% 7.56/1.49  
% 7.56/1.49  fof(f24,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.56/1.49    inference(ennf_transformation,[],[f15])).
% 7.56/1.49  
% 7.56/1.49  fof(f54,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.56/1.49    inference(cnf_transformation,[],[f24])).
% 7.56/1.49  
% 7.56/1.49  fof(f7,axiom,(
% 7.56/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f20,plain,(
% 7.56/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.56/1.49    inference(ennf_transformation,[],[f7])).
% 7.56/1.49  
% 7.56/1.49  fof(f21,plain,(
% 7.56/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.56/1.49    inference(flattening,[],[f20])).
% 7.56/1.49  
% 7.56/1.49  fof(f51,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f21])).
% 7.56/1.49  
% 7.56/1.49  fof(f4,axiom,(
% 7.56/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f17,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.56/1.49    inference(ennf_transformation,[],[f4])).
% 7.56/1.49  
% 7.56/1.49  fof(f48,plain,(
% 7.56/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f17])).
% 7.56/1.49  
% 7.56/1.49  fof(f5,axiom,(
% 7.56/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f49,plain,(
% 7.56/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.56/1.49    inference(cnf_transformation,[],[f5])).
% 7.56/1.49  
% 7.56/1.49  fof(f6,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f18,plain,(
% 7.56/1.49    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(ennf_transformation,[],[f6])).
% 7.56/1.49  
% 7.56/1.49  fof(f19,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.56/1.49    inference(flattening,[],[f18])).
% 7.56/1.49  
% 7.56/1.49  fof(f50,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f19])).
% 7.56/1.49  
% 7.56/1.49  fof(f2,axiom,(
% 7.56/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f46,plain,(
% 7.56/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f2])).
% 7.56/1.49  
% 7.56/1.49  fof(f67,plain,(
% 7.56/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f3,axiom,(
% 7.56/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f16,plain,(
% 7.56/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.56/1.49    inference(ennf_transformation,[],[f3])).
% 7.56/1.49  
% 7.56/1.49  fof(f47,plain,(
% 7.56/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.56/1.49    inference(cnf_transformation,[],[f16])).
% 7.56/1.49  
% 7.56/1.49  fof(f75,plain,(
% 7.56/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f1,axiom,(
% 7.56/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f33,plain,(
% 7.56/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.56/1.49    inference(nnf_transformation,[],[f1])).
% 7.56/1.49  
% 7.56/1.49  fof(f44,plain,(
% 7.56/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f33])).
% 7.56/1.49  
% 7.56/1.49  fof(f8,axiom,(
% 7.56/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f22,plain,(
% 7.56/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.56/1.49    inference(ennf_transformation,[],[f8])).
% 7.56/1.49  
% 7.56/1.49  fof(f23,plain,(
% 7.56/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.56/1.49    inference(flattening,[],[f22])).
% 7.56/1.49  
% 7.56/1.49  fof(f34,plain,(
% 7.56/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.56/1.49    inference(nnf_transformation,[],[f23])).
% 7.56/1.49  
% 7.56/1.49  fof(f52,plain,(
% 7.56/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f34])).
% 7.56/1.49  
% 7.56/1.49  fof(f68,plain,(
% 7.56/1.49    r1_subset_1(sK2,sK3)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f64,plain,(
% 7.56/1.49    ~v1_xboole_0(sK2)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f66,plain,(
% 7.56/1.49    ~v1_xboole_0(sK3)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f10,axiom,(
% 7.56/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f25,plain,(
% 7.56/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.56/1.49    inference(ennf_transformation,[],[f10])).
% 7.56/1.49  
% 7.56/1.49  fof(f26,plain,(
% 7.56/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.56/1.49    inference(flattening,[],[f25])).
% 7.56/1.49  
% 7.56/1.49  fof(f55,plain,(
% 7.56/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f26])).
% 7.56/1.49  
% 7.56/1.49  fof(f72,plain,(
% 7.56/1.49    v1_funct_1(sK5)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f71,plain,(
% 7.56/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f69,plain,(
% 7.56/1.49    v1_funct_1(sK4)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f12,axiom,(
% 7.56/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f29,plain,(
% 7.56/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.56/1.49    inference(ennf_transformation,[],[f12])).
% 7.56/1.49  
% 7.56/1.49  fof(f30,plain,(
% 7.56/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.56/1.49    inference(flattening,[],[f29])).
% 7.56/1.49  
% 7.56/1.49  fof(f61,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f30])).
% 7.56/1.49  
% 7.56/1.49  fof(f59,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f30])).
% 7.56/1.49  
% 7.56/1.49  fof(f63,plain,(
% 7.56/1.49    ~v1_xboole_0(sK1)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f73,plain,(
% 7.56/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f70,plain,(
% 7.56/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f62,plain,(
% 7.56/1.49    ~v1_xboole_0(sK0)),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f65,plain,(
% 7.56/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.56/1.49    inference(cnf_transformation,[],[f43])).
% 7.56/1.49  
% 7.56/1.49  fof(f11,axiom,(
% 7.56/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.56/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.49  
% 7.56/1.49  fof(f27,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.56/1.49    inference(ennf_transformation,[],[f11])).
% 7.56/1.49  
% 7.56/1.49  fof(f28,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.56/1.49    inference(flattening,[],[f27])).
% 7.56/1.49  
% 7.56/1.49  fof(f35,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.56/1.49    inference(nnf_transformation,[],[f28])).
% 7.56/1.49  
% 7.56/1.49  fof(f36,plain,(
% 7.56/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.56/1.49    inference(flattening,[],[f35])).
% 7.56/1.49  
% 7.56/1.49  fof(f56,plain,(
% 7.56/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f36])).
% 7.56/1.49  
% 7.56/1.49  fof(f79,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(equality_resolution,[],[f56])).
% 7.56/1.49  
% 7.56/1.49  fof(f60,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f30])).
% 7.56/1.49  
% 7.56/1.49  fof(f57,plain,(
% 7.56/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(cnf_transformation,[],[f36])).
% 7.56/1.49  
% 7.56/1.49  fof(f78,plain,(
% 7.56/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.56/1.49    inference(equality_resolution,[],[f57])).
% 7.56/1.49  
% 7.56/1.49  cnf(c_19,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.56/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_704,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1207,plain,
% 7.56/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10,plain,
% 7.56/1.49      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.56/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7,plain,
% 7.56/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_416,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ v1_relat_1(X0)
% 7.56/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.56/1.49      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_690,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | ~ v1_relat_1(X0_51)
% 7.56/1.49      | k7_relat_1(X0_51,X1_51) = X0_51 ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_416]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1221,plain,
% 7.56/1.49      ( k7_relat_1(X0_51,X1_51) = X0_51
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 7.56/1.49      | v1_relat_1(X0_51) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_690]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3494,plain,
% 7.56/1.49      ( k7_relat_1(sK5,sK3) = sK5 | v1_relat_1(sK5) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1207,c_1221]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_44,plain,
% 7.56/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_712,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 7.56/1.49      | ~ v1_relat_1(X1_51)
% 7.56/1.49      | v1_relat_1(X0_51) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1541,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | v1_relat_1(X0_51)
% 7.56/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1_51,X2_51)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_712]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1712,plain,
% 7.56/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.56/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 7.56/1.49      | v1_relat_1(sK5) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1541]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1713,plain,
% 7.56/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.56/1.49      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.56/1.49      | v1_relat_1(sK5) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_1712]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_5,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.56/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_711,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1752,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_711]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1753,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_1752]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3539,plain,
% 7.56/1.49      ( k7_relat_1(sK5,sK3) = sK5 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_3494,c_44,c_1713,c_1753]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1200,plain,
% 7.56/1.49      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 7.56/1.49      | v1_relat_1(X1_51) != iProver_top
% 7.56/1.49      | v1_relat_1(X0_51) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2405,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.56/1.49      | v1_relat_1(sK5) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1207,c_1200]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2928,plain,
% 7.56/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_2405,c_44,c_1713,c_1753]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_6,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.56/1.49      | ~ v1_relat_1(X2)
% 7.56/1.49      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2,plain,
% 7.56/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_463,plain,
% 7.56/1.49      ( ~ v1_relat_1(X0)
% 7.56/1.49      | X1 != X2
% 7.56/1.49      | k7_relat_1(k7_relat_1(X0,X2),X3) = k1_xboole_0
% 7.56/1.49      | k1_xboole_0 != X3 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_6,c_2]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_464,plain,
% 7.56/1.49      ( ~ v1_relat_1(X0)
% 7.56/1.49      | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_463]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_688,plain,
% 7.56/1.49      ( ~ v1_relat_1(X0_51)
% 7.56/1.49      | k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_464]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1223,plain,
% 7.56/1.49      ( k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0
% 7.56/1.49      | v1_relat_1(X0_51) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2933,plain,
% 7.56/1.49      ( k7_relat_1(k7_relat_1(sK5,X0_51),k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2928,c_1223]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4048,plain,
% 7.56/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3539,c_2933]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_26,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.56/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_698,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1213,plain,
% 7.56/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_713,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 7.56/1.49      | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1199,plain,
% 7.56/1.49      ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2387,plain,
% 7.56/1.49      ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1213,c_1199]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_18,negated_conjecture,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.56/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_705,negated_conjecture,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2753,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_2387,c_705]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_235,plain,
% 7.56/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.56/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_9,plain,
% 7.56/1.49      ( ~ r1_subset_1(X0,X1)
% 7.56/1.49      | r1_xboole_0(X0,X1)
% 7.56/1.49      | v1_xboole_0(X0)
% 7.56/1.49      | v1_xboole_0(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_25,negated_conjecture,
% 7.56/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_435,plain,
% 7.56/1.49      ( r1_xboole_0(X0,X1)
% 7.56/1.49      | v1_xboole_0(X0)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | sK3 != X1
% 7.56/1.49      | sK2 != X0 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_436,plain,
% 7.56/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_435]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_29,negated_conjecture,
% 7.56/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.56/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_27,negated_conjecture,
% 7.56/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_438,plain,
% 7.56/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_436,c_29,c_27]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_493,plain,
% 7.56/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 7.56/1.49      inference(resolution_lifted,[status(thm)],[c_235,c_438]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_494,plain,
% 7.56/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.56/1.49      inference(unflattening,[status(thm)],[c_493]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_685,plain,
% 7.56/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_494]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2754,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_2753,c_685]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.56/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_710,plain,
% 7.56/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | ~ v1_funct_1(X0_51)
% 7.56/1.49      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_11]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1202,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.56/1.49      | v1_funct_1(X2_51) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2481,plain,
% 7.56/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
% 7.56/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1207,c_1202]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_21,negated_conjecture,
% 7.56/1.49      ( v1_funct_1(sK5) ),
% 7.56/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1617,plain,
% 7.56/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.56/1.49      | ~ v1_funct_1(sK5)
% 7.56/1.49      | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_710]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1773,plain,
% 7.56/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.56/1.49      | ~ v1_funct_1(sK5)
% 7.56/1.49      | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1617]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3295,plain,
% 7.56/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_2481,c_21,c_19,c_1773]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_22,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.56/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_701,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1210,plain,
% 7.56/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2482,plain,
% 7.56/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1210,c_1202]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_24,negated_conjecture,
% 7.56/1.49      ( v1_funct_1(sK4) ),
% 7.56/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1622,plain,
% 7.56/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.56/1.49      | ~ v1_funct_1(sK4)
% 7.56/1.49      | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_710]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1778,plain,
% 7.56/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.56/1.49      | ~ v1_funct_1(sK4)
% 7.56/1.49      | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1622]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3372,plain,
% 7.56/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_2482,c_24,c_22,c_1778]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4017,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_2754,c_3295,c_3372]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4050,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_4048,c_4017]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_3495,plain,
% 7.56/1.49      ( k7_relat_1(sK4,sK2) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1210,c_1221]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_41,plain,
% 7.56/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1715,plain,
% 7.56/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.56/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 7.56/1.49      | v1_relat_1(sK4) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_1541]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1716,plain,
% 7.56/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.56/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_1715]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1755,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 7.56/1.49      inference(instantiation,[status(thm)],[c_711]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1756,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_1755]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4014,plain,
% 7.56/1.49      ( k7_relat_1(sK4,sK2) = sK4 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_3495,c_41,c_1716,c_1756]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2406,plain,
% 7.56/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.56/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1210,c_1200]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2941,plain,
% 7.56/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_2406,c_41,c_1716,c_1756]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2946,plain,
% 7.56/1.49      ( k7_relat_1(k7_relat_1(sK4,X0_51),k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2941,c_1223]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4106,plain,
% 7.56/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_4014,c_2946]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_16343,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.56/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4050,c_4106]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_16344,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_16343]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_15,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_708,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.56/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.56/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.56/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
% 7.56/1.49      | ~ v1_funct_1(X0_51)
% 7.56/1.49      | ~ v1_funct_1(X3_51)
% 7.56/1.49      | v1_xboole_0(X1_51)
% 7.56/1.49      | v1_xboole_0(X2_51)
% 7.56/1.49      | v1_xboole_0(X4_51)
% 7.56/1.49      | v1_xboole_0(X5_51) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1204,plain,
% 7.56/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 7.56/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 7.56/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
% 7.56/1.49      | v1_funct_1(X0_51) != iProver_top
% 7.56/1.49      | v1_funct_1(X3_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X5_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_2618,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 7.56/1.49      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 7.56/1.49      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 7.56/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.56/1.49      | v1_funct_1(X4_51) != iProver_top
% 7.56/1.49      | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1204,c_1202]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_17,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_706,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.56/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.56/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.56/1.49      | ~ v1_funct_1(X0_51)
% 7.56/1.49      | ~ v1_funct_1(X3_51)
% 7.56/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
% 7.56/1.49      | v1_xboole_0(X1_51)
% 7.56/1.49      | v1_xboole_0(X2_51)
% 7.56/1.49      | v1_xboole_0(X4_51)
% 7.56/1.49      | v1_xboole_0(X5_51) ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1206,plain,
% 7.56/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 7.56/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 7.56/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 7.56/1.49      | v1_funct_1(X0_51) != iProver_top
% 7.56/1.49      | v1_funct_1(X3_51) != iProver_top
% 7.56/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
% 7.56/1.49      | v1_xboole_0(X5_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7634,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 7.56/1.49      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 7.56/1.49      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 7.56/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.56/1.49      | v1_funct_1(X4_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_2618,c_1206]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7638,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 7.56/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 7.56/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.56/1.49      | v1_funct_1(sK5) != iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1207,c_7634]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_30,negated_conjecture,
% 7.56/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_33,plain,
% 7.56/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_36,plain,
% 7.56/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_42,plain,
% 7.56/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_20,negated_conjecture,
% 7.56/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_43,plain,
% 7.56/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7952,plain,
% 7.56/1.49      ( v1_funct_1(X2_51) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 7.56/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_7638,c_33,c_36,c_42,c_43]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7953,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 7.56/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_7952]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_7967,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1210,c_7953]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_34,plain,
% 7.56/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_39,plain,
% 7.56/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_23,negated_conjecture,
% 7.56/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_40,plain,
% 7.56/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_8323,plain,
% 7.56/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_7967,c_34,c_39,c_40]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_8324,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_8323]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_8333,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_1213,c_8324]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_31,negated_conjecture,
% 7.56/1.49      ( ~ v1_xboole_0(sK0) ),
% 7.56/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_32,plain,
% 7.56/1.49      ( v1_xboole_0(sK0) != iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_28,negated_conjecture,
% 7.56/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.56/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_35,plain,
% 7.56/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_8365,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_8333,c_32,c_35]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.56/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_16,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1) ),
% 7.56/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_174,plain,
% 7.56/1.49      ( ~ v1_funct_1(X3)
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_14,c_17,c_16,c_15]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_175,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_174]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_692,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.56/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.56/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.56/1.49      | ~ v1_funct_1(X0_51)
% 7.56/1.49      | ~ v1_funct_1(X3_51)
% 7.56/1.49      | v1_xboole_0(X1_51)
% 7.56/1.49      | v1_xboole_0(X2_51)
% 7.56/1.49      | v1_xboole_0(X4_51)
% 7.56/1.49      | v1_xboole_0(X5_51)
% 7.56/1.49      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_175]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1219,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
% 7.56/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 7.56/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 7.56/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 7.56/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.56/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_4184,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_funct_1(sK5) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3295,c_1219]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10436,plain,
% 7.56/1.49      ( v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_4184,c_33,c_36,c_42,c_43,c_44]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10437,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_10436]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10457,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2387,c_10437]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10467,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_10457,c_2387]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_37,plain,
% 7.56/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11073,plain,
% 7.56/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_10467,c_32,c_37]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11074,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_11073]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11087,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3372,c_11074]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11171,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k1_xboole_0 != k1_xboole_0
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_11087,c_685,c_4048,c_4106]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11172,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(equality_resolution_simp,[status(thm)],[c_11171]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11173,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_11172,c_8365]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_10452,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3372,c_10437]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11055,plain,
% 7.56/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_10452,c_34,c_39,c_40,c_41]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11056,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_11055]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11066,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2387,c_11056]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11067,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_11066,c_685,c_4048]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11068,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_11067,c_2387,c_8365]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11069,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | k1_xboole_0 != k1_xboole_0
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_11068,c_685,c_4106]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11070,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(equality_resolution_simp,[status(thm)],[c_11069]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_11255,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_11173,c_32,c_35,c_37,c_11070]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_13,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.56/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_181,plain,
% 7.56/1.49      ( ~ v1_funct_1(X3)
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_13,c_17,c_16,c_15]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_182,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.56/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.56/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.56/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.56/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.56/1.49      | ~ v1_funct_1(X0)
% 7.56/1.49      | ~ v1_funct_1(X3)
% 7.56/1.49      | v1_xboole_0(X1)
% 7.56/1.49      | v1_xboole_0(X2)
% 7.56/1.49      | v1_xboole_0(X4)
% 7.56/1.49      | v1_xboole_0(X5)
% 7.56/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_181]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_691,plain,
% 7.56/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.56/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.56/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.56/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.56/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.56/1.49      | ~ v1_funct_1(X0_51)
% 7.56/1.49      | ~ v1_funct_1(X3_51)
% 7.56/1.49      | v1_xboole_0(X1_51)
% 7.56/1.49      | v1_xboole_0(X2_51)
% 7.56/1.49      | v1_xboole_0(X4_51)
% 7.56/1.49      | v1_xboole_0(X5_51)
% 7.56/1.49      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
% 7.56/1.49      inference(subtyping,[status(esa)],[c_182]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_1220,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
% 7.56/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 7.56/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 7.56/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.56/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 7.56/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.56/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_5811,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_funct_1(sK5) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3295,c_1220]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14191,plain,
% 7.56/1.49      ( v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_5811,c_33,c_36,c_42,c_43,c_44]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14192,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_14191]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14212,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2387,c_14192]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14222,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_14212,c_2387]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14409,plain,
% 7.56/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_14222,c_32,c_37]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14410,plain,
% 7.56/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.56/1.49      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_14409]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14423,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3372,c_14410]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14507,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k1_xboole_0 != k1_xboole_0
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_14423,c_685,c_4048,c_4106]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14508,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(equality_resolution_simp,[status(thm)],[c_14507]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14509,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_14508,c_8365]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14207,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.56/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.56/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_funct_1(sK4) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_3372,c_14192]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14341,plain,
% 7.56/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.56/1.49      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_14207,c_34,c_39,c_40,c_41]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14342,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.56/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.56/1.49      inference(renaming,[status(thm)],[c_14341]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14352,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(superposition,[status(thm)],[c_2387,c_14342]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14353,plain,
% 7.56/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_14352,c_685,c_4048]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14354,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_14353,c_2387,c_8365]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14355,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | k1_xboole_0 != k1_xboole_0
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(light_normalisation,[status(thm)],[c_14354,c_685,c_4106]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14356,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.56/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.56/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.56/1.49      inference(equality_resolution_simp,[status(thm)],[c_14355]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_14525,plain,
% 7.56/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 7.56/1.49      inference(global_propositional_subsumption,
% 7.56/1.49                [status(thm)],
% 7.56/1.49                [c_14509,c_32,c_35,c_37,c_14356]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_16345,plain,
% 7.56/1.49      ( sK5 != sK5 | sK4 != sK4 ),
% 7.56/1.49      inference(demodulation,[status(thm)],[c_16344,c_8365,c_11255,c_14525]) ).
% 7.56/1.49  
% 7.56/1.49  cnf(c_16346,plain,
% 7.56/1.49      ( $false ),
% 7.56/1.49      inference(equality_resolution_simp,[status(thm)],[c_16345]) ).
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.49  
% 7.56/1.49  ------                               Statistics
% 7.56/1.49  
% 7.56/1.49  ------ General
% 7.56/1.49  
% 7.56/1.49  abstr_ref_over_cycles:                  0
% 7.56/1.49  abstr_ref_under_cycles:                 0
% 7.56/1.49  gc_basic_clause_elim:                   0
% 7.56/1.49  forced_gc_time:                         0
% 7.56/1.49  parsing_time:                           0.013
% 7.56/1.49  unif_index_cands_time:                  0.
% 7.56/1.49  unif_index_add_time:                    0.
% 7.56/1.49  orderings_time:                         0.
% 7.56/1.49  out_proof_time:                         0.022
% 7.56/1.49  total_time:                             0.876
% 7.56/1.49  num_of_symbols:                         56
% 7.56/1.49  num_of_terms:                           32593
% 7.56/1.49  
% 7.56/1.49  ------ Preprocessing
% 7.56/1.49  
% 7.56/1.49  num_of_splits:                          0
% 7.56/1.49  num_of_split_atoms:                     0
% 7.56/1.49  num_of_reused_defs:                     0
% 7.56/1.49  num_eq_ax_congr_red:                    6
% 7.56/1.49  num_of_sem_filtered_clauses:            1
% 7.56/1.49  num_of_subtypes:                        2
% 7.56/1.49  monotx_restored_types:                  0
% 7.56/1.49  sat_num_of_epr_types:                   0
% 7.56/1.49  sat_num_of_non_cyclic_types:            0
% 7.56/1.49  sat_guarded_non_collapsed_types:        1
% 7.56/1.49  num_pure_diseq_elim:                    0
% 7.56/1.49  simp_replaced_by:                       0
% 7.56/1.49  res_preprocessed:                       152
% 7.56/1.49  prep_upred:                             0
% 7.56/1.49  prep_unflattend:                        10
% 7.56/1.49  smt_new_axioms:                         0
% 7.56/1.49  pred_elim_cands:                        5
% 7.56/1.49  pred_elim:                              3
% 7.56/1.49  pred_elim_cl:                           3
% 7.56/1.49  pred_elim_cycles:                       5
% 7.56/1.49  merged_defs:                            2
% 7.56/1.49  merged_defs_ncl:                        0
% 7.56/1.49  bin_hyper_res:                          2
% 7.56/1.49  prep_cycles:                            4
% 7.56/1.49  pred_elim_time:                         0.003
% 7.56/1.49  splitting_time:                         0.
% 7.56/1.49  sem_filter_time:                        0.
% 7.56/1.49  monotx_time:                            0.
% 7.56/1.49  subtype_inf_time:                       0.001
% 7.56/1.49  
% 7.56/1.49  ------ Problem properties
% 7.56/1.49  
% 7.56/1.49  clauses:                                29
% 7.56/1.49  conjectures:                            13
% 7.56/1.49  epr:                                    8
% 7.56/1.49  horn:                                   23
% 7.56/1.49  ground:                                 14
% 7.56/1.49  unary:                                  15
% 7.56/1.49  binary:                                 3
% 7.56/1.49  lits:                                   120
% 7.56/1.49  lits_eq:                                18
% 7.56/1.49  fd_pure:                                0
% 7.56/1.49  fd_pseudo:                              0
% 7.56/1.49  fd_cond:                                0
% 7.56/1.49  fd_pseudo_cond:                         0
% 7.56/1.49  ac_symbols:                             0
% 7.56/1.49  
% 7.56/1.49  ------ Propositional Solver
% 7.56/1.49  
% 7.56/1.49  prop_solver_calls:                      27
% 7.56/1.49  prop_fast_solver_calls:                 3295
% 7.56/1.49  smt_solver_calls:                       0
% 7.56/1.49  smt_fast_solver_calls:                  0
% 7.56/1.49  prop_num_of_clauses:                    6516
% 7.56/1.49  prop_preprocess_simplified:             10443
% 7.56/1.49  prop_fo_subsumed:                       251
% 7.56/1.49  prop_solver_time:                       0.
% 7.56/1.49  smt_solver_time:                        0.
% 7.56/1.49  smt_fast_solver_time:                   0.
% 7.56/1.49  prop_fast_solver_time:                  0.
% 7.56/1.49  prop_unsat_core_time:                   0.
% 7.56/1.49  
% 7.56/1.49  ------ QBF
% 7.56/1.49  
% 7.56/1.49  qbf_q_res:                              0
% 7.56/1.49  qbf_num_tautologies:                    0
% 7.56/1.49  qbf_prep_cycles:                        0
% 7.56/1.49  
% 7.56/1.49  ------ BMC1
% 7.56/1.49  
% 7.56/1.49  bmc1_current_bound:                     -1
% 7.56/1.49  bmc1_last_solved_bound:                 -1
% 7.56/1.49  bmc1_unsat_core_size:                   -1
% 7.56/1.49  bmc1_unsat_core_parents_size:           -1
% 7.56/1.49  bmc1_merge_next_fun:                    0
% 7.56/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.56/1.49  
% 7.56/1.49  ------ Instantiation
% 7.56/1.49  
% 7.56/1.49  inst_num_of_clauses:                    1444
% 7.56/1.49  inst_num_in_passive:                    44
% 7.56/1.49  inst_num_in_active:                     747
% 7.56/1.49  inst_num_in_unprocessed:                653
% 7.56/1.49  inst_num_of_loops:                      760
% 7.56/1.49  inst_num_of_learning_restarts:          0
% 7.56/1.49  inst_num_moves_active_passive:          8
% 7.56/1.49  inst_lit_activity:                      0
% 7.56/1.49  inst_lit_activity_moves:                0
% 7.56/1.49  inst_num_tautologies:                   0
% 7.56/1.49  inst_num_prop_implied:                  0
% 7.56/1.49  inst_num_existing_simplified:           0
% 7.56/1.49  inst_num_eq_res_simplified:             0
% 7.56/1.49  inst_num_child_elim:                    0
% 7.56/1.49  inst_num_of_dismatching_blockings:      152
% 7.56/1.49  inst_num_of_non_proper_insts:           1063
% 7.56/1.49  inst_num_of_duplicates:                 0
% 7.56/1.49  inst_inst_num_from_inst_to_res:         0
% 7.56/1.49  inst_dismatching_checking_time:         0.
% 7.56/1.49  
% 7.56/1.49  ------ Resolution
% 7.56/1.49  
% 7.56/1.49  res_num_of_clauses:                     0
% 7.56/1.49  res_num_in_passive:                     0
% 7.56/1.49  res_num_in_active:                      0
% 7.56/1.49  res_num_of_loops:                       156
% 7.56/1.49  res_forward_subset_subsumed:            54
% 7.56/1.49  res_backward_subset_subsumed:           2
% 7.56/1.49  res_forward_subsumed:                   0
% 7.56/1.49  res_backward_subsumed:                  0
% 7.56/1.49  res_forward_subsumption_resolution:     0
% 7.56/1.49  res_backward_subsumption_resolution:    0
% 7.56/1.49  res_clause_to_clause_subsumption:       2398
% 7.56/1.49  res_orphan_elimination:                 0
% 7.56/1.49  res_tautology_del:                      40
% 7.56/1.49  res_num_eq_res_simplified:              0
% 7.56/1.49  res_num_sel_changes:                    0
% 7.56/1.49  res_moves_from_active_to_pass:          0
% 7.56/1.49  
% 7.56/1.49  ------ Superposition
% 7.56/1.49  
% 7.56/1.49  sup_time_total:                         0.
% 7.56/1.49  sup_time_generating:                    0.
% 7.56/1.49  sup_time_sim_full:                      0.
% 7.56/1.49  sup_time_sim_immed:                     0.
% 7.56/1.49  
% 7.56/1.49  sup_num_of_clauses:                     274
% 7.56/1.49  sup_num_in_active:                      149
% 7.56/1.49  sup_num_in_passive:                     125
% 7.56/1.49  sup_num_of_loops:                       151
% 7.56/1.49  sup_fw_superposition:                   256
% 7.56/1.49  sup_bw_superposition:                   46
% 7.56/1.49  sup_immediate_simplified:               135
% 7.56/1.49  sup_given_eliminated:                   0
% 7.56/1.49  comparisons_done:                       0
% 7.56/1.49  comparisons_avoided:                    0
% 7.56/1.49  
% 7.56/1.49  ------ Simplifications
% 7.56/1.49  
% 7.56/1.49  
% 7.56/1.49  sim_fw_subset_subsumed:                 0
% 7.56/1.49  sim_bw_subset_subsumed:                 2
% 7.56/1.49  sim_fw_subsumed:                        16
% 7.56/1.49  sim_bw_subsumed:                        8
% 7.56/1.49  sim_fw_subsumption_res:                 7
% 7.56/1.49  sim_bw_subsumption_res:                 0
% 7.56/1.49  sim_tautology_del:                      0
% 7.56/1.49  sim_eq_tautology_del:                   7
% 7.56/1.49  sim_eq_res_simp:                        7
% 7.56/1.49  sim_fw_demodulated:                     84
% 7.56/1.49  sim_bw_demodulated:                     2
% 7.56/1.49  sim_light_normalised:                   52
% 7.56/1.49  sim_joinable_taut:                      0
% 7.56/1.49  sim_joinable_simp:                      0
% 7.56/1.49  sim_ac_normalised:                      0
% 7.56/1.49  sim_smt_subsumption:                    0
% 7.56/1.49  
%------------------------------------------------------------------------------
