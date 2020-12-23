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
% DateTime   : Thu Dec  3 12:21:27 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  264 (6088 expanded)
%              Number of clauses        :  179 (1660 expanded)
%              Number of leaves         :   22 (2268 expanded)
%              Depth                    :   23
%              Number of atoms          : 1272 (73119 expanded)
%              Number of equality atoms :  489 (16763 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f50,f49,f48,f47,f46,f45])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

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

fof(f71,plain,(
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

fof(f93,plain,(
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
    inference(equality_resolution,[],[f71])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
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
    inference(flattening,[],[f36])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
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

fof(f94,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f89,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_657,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1561,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1537,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_684])).

cnf(c_2267,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
    inference(superposition,[status(thm)],[c_1561,c_1537])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_664,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1554,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1549,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_4680,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1549])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2086,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_2347,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(instantiation,[status(thm)],[c_2086])).

cnf(c_4855,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4680,c_27,c_25,c_2347])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_661,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1557,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_661])).

cnf(c_4681,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1549])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2091,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_2352,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(instantiation,[status(thm)],[c_2091])).

cnf(c_4861,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4681,c_30,c_28,c_2352])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_23,plain,
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
    inference(cnf_transformation,[],[f73])).

cnf(c_22,plain,
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
    inference(cnf_transformation,[],[f74])).

cnf(c_21,plain,
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
    inference(cnf_transformation,[],[f75])).

cnf(c_377,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_23,c_22,c_21])).

cnf(c_378,plain,
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
    inference(renaming,[status(thm)],[c_377])).

cnf(c_650,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_378])).

cnf(c_1568,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1538,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
    | v1_xboole_0(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_1811,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
    | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X4_54) = X5_54
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1568,c_1538])).

cnf(c_9134,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4861,c_1811])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_39,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_46,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_47,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_15212,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9134,c_39,c_40,c_45,c_46,c_47])).

cnf(c_15213,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_15212])).

cnf(c_15226,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4855,c_15213])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_42,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_48,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_49,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_50,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15426,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15226,c_42,c_48,c_49,c_50])).

cnf(c_15436,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_15426])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_658,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1560,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_658])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_676,plain,
    ( ~ r1_subset_1(X0_54,X1_54)
    | r1_xboole_0(X0_54,X1_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1543,plain,
    ( r1_subset_1(X0_54,X1_54) != iProver_top
    | r1_xboole_0(X0_54,X1_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_4203,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1560,c_1543])).

cnf(c_44,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2018,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_2019,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2018])).

cnf(c_5061,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4203,c_40,c_42,c_44,c_2019])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_685,plain,
    ( ~ r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1536,plain,
    ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_5067,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5061,c_1536])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_673,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | v1_partfun1(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | v1_xboole_0(X2_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1546,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_partfun1(X0_54,X1_54) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_4702,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1546])).

cnf(c_2096,plain,
    ( ~ v1_funct_2(sK5,X0_54,X1_54)
    | v1_partfun1(sK5,X0_54)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_54) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_2357,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_2358,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2357])).

cnf(c_5164,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4702,c_39,c_48,c_49,c_50,c_2358])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_671,plain,
    ( ~ v1_partfun1(X0_54,X1_54)
    | ~ v4_relat_1(X0_54,X1_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X1_54 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1548,plain,
    ( k1_relat_1(X0_54) = X1_54
    | v1_partfun1(X0_54,X1_54) != iProver_top
    | v4_relat_1(X0_54,X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_5169,plain,
    ( k1_relat_1(sK5) = sK3
    | v4_relat_1(sK5,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5164,c_1548])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1964,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_674,plain,
    ( v4_relat_1(X0_54,X1_54)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1996,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_2189,plain,
    ( ~ v1_partfun1(sK5,X0_54)
    | ~ v4_relat_1(sK5,X0_54)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = X0_54 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_2733,plain,
    ( ~ v1_partfun1(sK5,sK3)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_5295,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5169,c_36,c_27,c_26,c_25,c_1964,c_1996,c_2357,c_2733])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_682,plain,
    ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1539,plain,
    ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
    | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_5316,plain,
    ( k7_relat_1(sK5,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5295,c_1539])).

cnf(c_1965,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1964])).

cnf(c_5639,plain,
    ( r1_xboole_0(X0_54,sK3) != iProver_top
    | k7_relat_1(sK5,X0_54) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5316,c_50,c_1965])).

cnf(c_5640,plain,
    ( k7_relat_1(sK5,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5639])).

cnf(c_5647,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5061,c_5640])).

cnf(c_1544,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_2762,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1544])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_681,plain,
    ( ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,k3_xboole_0(k1_relat_1(X0_54),X1_54)) = k7_relat_1(X0_54,X1_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1540,plain,
    ( k7_relat_1(X0_54,k3_xboole_0(k1_relat_1(X0_54),X1_54)) = k7_relat_1(X0_54,X1_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_3578,plain,
    ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_54)) = k7_relat_1(sK5,X0_54) ),
    inference(superposition,[status(thm)],[c_2762,c_1540])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_678,plain,
    ( ~ v1_relat_1(X0_54)
    | k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1541,plain,
    ( k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_2841,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0_54)) = k3_xboole_0(k1_relat_1(sK5),X0_54) ),
    inference(superposition,[status(thm)],[c_2762,c_1541])).

cnf(c_3584,plain,
    ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0_54))) = k7_relat_1(sK5,X0_54) ),
    inference(light_normalisation,[status(thm)],[c_3578,c_2841])).

cnf(c_5748,plain,
    ( k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) = k7_relat_1(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_5647,c_3584])).

cnf(c_7,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_679,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_5749,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5748,c_679,c_5647])).

cnf(c_15437,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15436,c_5067,c_5749])).

cnf(c_4703,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1546])).

cnf(c_2101,plain,
    ( ~ v1_funct_2(sK4,X0_54,X1_54)
    | v1_partfun1(sK4,X0_54)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_54) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_2360,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_2361,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2360])).

cnf(c_5172,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4703,c_39,c_45,c_46,c_47,c_2361])).

cnf(c_5177,plain,
    ( k1_relat_1(sK4) = sK2
    | v4_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5172,c_1548])).

cnf(c_1967,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1999,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_2223,plain,
    ( ~ v1_partfun1(sK4,X0_54)
    | ~ v4_relat_1(sK4,X0_54)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0_54 ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_2235,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2223])).

cnf(c_5428,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5177,c_36,c_30,c_29,c_28,c_1967,c_1999,c_2235,c_2360])).

cnf(c_2763,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1544])).

cnf(c_2845,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(k1_relat_1(sK4),X0_54) ),
    inference(superposition,[status(thm)],[c_2763,c_1541])).

cnf(c_5433,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(sK2,X0_54) ),
    inference(demodulation,[status(thm)],[c_5428,c_2845])).

cnf(c_3579,plain,
    ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_54)) = k7_relat_1(sK4,X0_54) ),
    inference(superposition,[status(thm)],[c_2763,c_1540])).

cnf(c_3581,plain,
    ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0_54))) = k7_relat_1(sK4,X0_54) ),
    inference(light_normalisation,[status(thm)],[c_3579,c_2845])).

cnf(c_6303,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_54)) = k7_relat_1(sK4,X0_54) ),
    inference(demodulation,[status(thm)],[c_5433,c_3581])).

cnf(c_15438,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15437,c_2267,c_6303])).

cnf(c_5300,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0_54)) = k3_xboole_0(sK3,X0_54) ),
    inference(demodulation,[status(thm)],[c_5295,c_2841])).

cnf(c_6036,plain,
    ( k3_xboole_0(sK3,sK2) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5647,c_5300])).

cnf(c_6057,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6036,c_679])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_686,plain,
    ( r1_xboole_0(X0_54,X1_54)
    | k3_xboole_0(X0_54,X1_54) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1535,plain,
    ( k3_xboole_0(X0_54,X1_54) != k1_xboole_0
    | r1_xboole_0(X0_54,X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_6369,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6057,c_1535])).

cnf(c_5449,plain,
    ( k7_relat_1(sK4,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5428,c_1539])).

cnf(c_1968,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1967])).

cnf(c_5649,plain,
    ( r1_xboole_0(X0_54,sK2) != iProver_top
    | k7_relat_1(sK4,X0_54) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5449,c_47,c_1968])).

cnf(c_5650,plain,
    ( k7_relat_1(sK4,X0_54) = k1_xboole_0
    | r1_xboole_0(X0_54,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5649])).

cnf(c_6754,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6369,c_5650])).

cnf(c_15439,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15438,c_6754])).

cnf(c_15440,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15439])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f94])).

cnf(c_368,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23,c_22,c_21])).

cnf(c_369,plain,
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
    inference(renaming,[status(thm)],[c_368])).

cnf(c_651,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_369])).

cnf(c_1567,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
    | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_651])).

cnf(c_1783,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
    | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X0_54) = X2_54
    | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
    | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1567,c_1538])).

cnf(c_7219,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4861,c_1783])).

cnf(c_8985,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7219,c_39,c_40,c_45,c_46,c_47])).

cnf(c_8986,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
    | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_8985])).

cnf(c_8999,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4855,c_8986])).

cnf(c_10274,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8999,c_42,c_48,c_49,c_50])).

cnf(c_10284,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2267,c_10274])).

cnf(c_10285,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10284,c_5067,c_5749])).

cnf(c_10286,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10285,c_2267,c_6303])).

cnf(c_10287,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10286,c_6754])).

cnf(c_10288,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10287])).

cnf(c_6470,plain,
    ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5067,c_6303])).

cnf(c_6957,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6754,c_6470])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_665,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_2479,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2267,c_665])).

cnf(c_4859,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4855,c_2479])).

cnf(c_5056,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4859,c_4861])).

cnf(c_5292,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5067,c_5056])).

cnf(c_6326,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5292,c_5749])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15440,c_10288,c_6957,c_6326,c_43,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.87/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.49  
% 7.87/1.49  ------  iProver source info
% 7.87/1.49  
% 7.87/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.49  git: non_committed_changes: false
% 7.87/1.49  git: last_make_outside_of_git: false
% 7.87/1.49  
% 7.87/1.49  ------ 
% 7.87/1.49  ------ Parsing...
% 7.87/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.49  
% 7.87/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.87/1.49  ------ Proving...
% 7.87/1.49  ------ Problem Properties 
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  clauses                                 37
% 7.87/1.49  conjectures                             14
% 7.87/1.49  EPR                                     11
% 7.87/1.49  Horn                                    28
% 7.87/1.49  unary                                   15
% 7.87/1.49  binary                                  7
% 7.87/1.49  lits                                    145
% 7.87/1.49  lits eq                                 19
% 7.87/1.49  fd_pure                                 0
% 7.87/1.49  fd_pseudo                               0
% 7.87/1.49  fd_cond                                 0
% 7.87/1.49  fd_pseudo_cond                          1
% 7.87/1.49  AC symbols                              0
% 7.87/1.49  
% 7.87/1.49  ------ Input Options Time Limit: Unbounded
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  ------ 
% 7.87/1.49  Current options:
% 7.87/1.49  ------ 
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  ------ Proving...
% 7.87/1.49  
% 7.87/1.49  
% 7.87/1.49  % SZS status Theorem for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.49  
% 7.87/1.49  fof(f16,conjecture,(
% 7.87/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f17,negated_conjecture,(
% 7.87/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.87/1.49    inference(negated_conjecture,[],[f16])).
% 7.87/1.49  
% 7.87/1.49  fof(f38,plain,(
% 7.87/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.87/1.49    inference(ennf_transformation,[],[f17])).
% 7.87/1.49  
% 7.87/1.49  fof(f39,plain,(
% 7.87/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.87/1.49    inference(flattening,[],[f38])).
% 7.87/1.49  
% 7.87/1.49  fof(f50,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f49,plain,(
% 7.87/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f48,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f47,plain,(
% 7.87/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f46,plain,(
% 7.87/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f45,plain,(
% 7.87/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.87/1.49    introduced(choice_axiom,[])).
% 7.87/1.49  
% 7.87/1.49  fof(f51,plain,(
% 7.87/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.87/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f50,f49,f48,f47,f46,f45])).
% 7.87/1.49  
% 7.87/1.49  fof(f81,plain,(
% 7.87/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f2,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f19,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.87/1.49    inference(ennf_transformation,[],[f2])).
% 7.87/1.49  
% 7.87/1.49  fof(f54,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f19])).
% 7.87/1.49  
% 7.87/1.49  fof(f88,plain,(
% 7.87/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f13,axiom,(
% 7.87/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f32,plain,(
% 7.87/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.87/1.49    inference(ennf_transformation,[],[f13])).
% 7.87/1.49  
% 7.87/1.49  fof(f33,plain,(
% 7.87/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.87/1.49    inference(flattening,[],[f32])).
% 7.87/1.49  
% 7.87/1.49  fof(f69,plain,(
% 7.87/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f33])).
% 7.87/1.49  
% 7.87/1.49  fof(f86,plain,(
% 7.87/1.49    v1_funct_1(sK5)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f85,plain,(
% 7.87/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f83,plain,(
% 7.87/1.49    v1_funct_1(sK4)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f14,axiom,(
% 7.87/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f34,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.87/1.49    inference(ennf_transformation,[],[f14])).
% 7.87/1.49  
% 7.87/1.49  fof(f35,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.87/1.49    inference(flattening,[],[f34])).
% 7.87/1.49  
% 7.87/1.49  fof(f43,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.87/1.49    inference(nnf_transformation,[],[f35])).
% 7.87/1.49  
% 7.87/1.49  fof(f44,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.87/1.49    inference(flattening,[],[f43])).
% 7.87/1.49  
% 7.87/1.49  fof(f71,plain,(
% 7.87/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f44])).
% 7.87/1.49  
% 7.87/1.49  fof(f93,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(equality_resolution,[],[f71])).
% 7.87/1.49  
% 7.87/1.49  fof(f15,axiom,(
% 7.87/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f36,plain,(
% 7.87/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.87/1.49    inference(ennf_transformation,[],[f15])).
% 7.87/1.49  
% 7.87/1.49  fof(f37,plain,(
% 7.87/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.87/1.49    inference(flattening,[],[f36])).
% 7.87/1.49  
% 7.87/1.49  fof(f73,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f37])).
% 7.87/1.49  
% 7.87/1.49  fof(f74,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f37])).
% 7.87/1.49  
% 7.87/1.49  fof(f75,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f37])).
% 7.87/1.49  
% 7.87/1.49  fof(f3,axiom,(
% 7.87/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f20,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.87/1.49    inference(ennf_transformation,[],[f3])).
% 7.87/1.49  
% 7.87/1.49  fof(f55,plain,(
% 7.87/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f20])).
% 7.87/1.49  
% 7.87/1.49  fof(f77,plain,(
% 7.87/1.49    ~v1_xboole_0(sK1)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f78,plain,(
% 7.87/1.49    ~v1_xboole_0(sK2)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f84,plain,(
% 7.87/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f80,plain,(
% 7.87/1.49    ~v1_xboole_0(sK3)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f87,plain,(
% 7.87/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f82,plain,(
% 7.87/1.49    r1_subset_1(sK2,sK3)),
% 7.87/1.49    inference(cnf_transformation,[],[f51])).
% 7.87/1.49  
% 7.87/1.49  fof(f8,axiom,(
% 7.87/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f24,plain,(
% 7.87/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.87/1.49    inference(ennf_transformation,[],[f8])).
% 7.87/1.49  
% 7.87/1.49  fof(f25,plain,(
% 7.87/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.87/1.49    inference(flattening,[],[f24])).
% 7.87/1.49  
% 7.87/1.49  fof(f41,plain,(
% 7.87/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.87/1.49    inference(nnf_transformation,[],[f25])).
% 7.87/1.49  
% 7.87/1.49  fof(f61,plain,(
% 7.87/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f41])).
% 7.87/1.49  
% 7.87/1.49  fof(f1,axiom,(
% 7.87/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f40,plain,(
% 7.87/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.87/1.49    inference(nnf_transformation,[],[f1])).
% 7.87/1.49  
% 7.87/1.49  fof(f52,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f40])).
% 7.87/1.49  
% 7.87/1.49  fof(f11,axiom,(
% 7.87/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f28,plain,(
% 7.87/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.87/1.49    inference(ennf_transformation,[],[f11])).
% 7.87/1.49  
% 7.87/1.49  fof(f29,plain,(
% 7.87/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.87/1.49    inference(flattening,[],[f28])).
% 7.87/1.49  
% 7.87/1.49  fof(f66,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f29])).
% 7.87/1.49  
% 7.87/1.49  fof(f12,axiom,(
% 7.87/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f30,plain,(
% 7.87/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.87/1.49    inference(ennf_transformation,[],[f12])).
% 7.87/1.49  
% 7.87/1.49  fof(f31,plain,(
% 7.87/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(flattening,[],[f30])).
% 7.87/1.49  
% 7.87/1.49  fof(f42,plain,(
% 7.87/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(nnf_transformation,[],[f31])).
% 7.87/1.49  
% 7.87/1.49  fof(f67,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f42])).
% 7.87/1.49  
% 7.87/1.49  fof(f9,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f26,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(ennf_transformation,[],[f9])).
% 7.87/1.49  
% 7.87/1.49  fof(f63,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f26])).
% 7.87/1.49  
% 7.87/1.49  fof(f10,axiom,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f18,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.87/1.49    inference(pure_predicate_removal,[],[f10])).
% 7.87/1.49  
% 7.87/1.49  fof(f27,plain,(
% 7.87/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.87/1.49    inference(ennf_transformation,[],[f18])).
% 7.87/1.49  
% 7.87/1.49  fof(f64,plain,(
% 7.87/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.87/1.49    inference(cnf_transformation,[],[f27])).
% 7.87/1.49  
% 7.87/1.49  fof(f4,axiom,(
% 7.87/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f21,plain,(
% 7.87/1.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.87/1.49    inference(ennf_transformation,[],[f4])).
% 7.87/1.49  
% 7.87/1.49  fof(f56,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f21])).
% 7.87/1.49  
% 7.87/1.49  fof(f5,axiom,(
% 7.87/1.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f22,plain,(
% 7.87/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(ennf_transformation,[],[f5])).
% 7.87/1.49  
% 7.87/1.49  fof(f57,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f22])).
% 7.87/1.49  
% 7.87/1.49  fof(f7,axiom,(
% 7.87/1.49    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f23,plain,(
% 7.87/1.49    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 7.87/1.49    inference(ennf_transformation,[],[f7])).
% 7.87/1.49  
% 7.87/1.49  fof(f60,plain,(
% 7.87/1.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f23])).
% 7.87/1.49  
% 7.87/1.49  fof(f6,axiom,(
% 7.87/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.87/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.49  
% 7.87/1.49  fof(f58,plain,(
% 7.87/1.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.87/1.49    inference(cnf_transformation,[],[f6])).
% 7.87/1.49  
% 7.87/1.49  fof(f53,plain,(
% 7.87/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.87/1.49    inference(cnf_transformation,[],[f40])).
% 7.87/1.49  
% 7.87/1.49  fof(f70,plain,(
% 7.87/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.49    inference(cnf_transformation,[],[f44])).
% 7.87/1.49  
% 7.87/1.49  fof(f94,plain,(
% 7.87/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.87/1.50    inference(equality_resolution,[],[f70])).
% 7.87/1.50  
% 7.87/1.50  fof(f89,plain,(
% 7.87/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.87/1.50    inference(cnf_transformation,[],[f51])).
% 7.87/1.50  
% 7.87/1.50  fof(f79,plain,(
% 7.87/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.87/1.50    inference(cnf_transformation,[],[f51])).
% 7.87/1.50  
% 7.87/1.50  cnf(c_32,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.87/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_657,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_32]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1561,plain,
% 7.87/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.87/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_684,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.87/1.50      | k9_subset_1(X1_54,X2_54,X0_54) = k3_xboole_0(X2_54,X0_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1537,plain,
% 7.87/1.50      ( k9_subset_1(X0_54,X1_54,X2_54) = k3_xboole_0(X1_54,X2_54)
% 7.87/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_684]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2267,plain,
% 7.87/1.50      ( k9_subset_1(sK0,X0_54,sK3) = k3_xboole_0(X0_54,sK3) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1561,c_1537]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_25,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.87/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_664,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_25]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1554,plain,
% 7.87/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_17,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.87/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_670,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.87/1.50      | ~ v1_funct_1(X0_54)
% 7.87/1.50      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1549,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.87/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.87/1.50      | v1_funct_1(X2_54) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4680,plain,
% 7.87/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 7.87/1.50      | v1_funct_1(sK5) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1554,c_1549]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_27,negated_conjecture,
% 7.87/1.50      ( v1_funct_1(sK5) ),
% 7.87/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2086,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.87/1.50      | ~ v1_funct_1(sK5)
% 7.87/1.50      | k2_partfun1(X0_54,X1_54,sK5,X2_54) = k7_relat_1(sK5,X2_54) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_670]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2347,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.87/1.50      | ~ v1_funct_1(sK5)
% 7.87/1.50      | k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2086]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4855,plain,
% 7.87/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_4680,c_27,c_25,c_2347]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_28,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.87/1.50      inference(cnf_transformation,[],[f85]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_661,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_28]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1557,plain,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_661]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4681,plain,
% 7.87/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 7.87/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1557,c_1549]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_30,negated_conjecture,
% 7.87/1.50      ( v1_funct_1(sK4) ),
% 7.87/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2091,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.87/1.50      | ~ v1_funct_1(sK4)
% 7.87/1.50      | k2_partfun1(X0_54,X1_54,sK4,X2_54) = k7_relat_1(sK4,X2_54) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_670]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2352,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.87/1.50      | ~ v1_funct_1(sK4)
% 7.87/1.50      | k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2091]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4861,plain,
% 7.87/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_4681,c_30,c_28,c_2352]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_19,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_23,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_22,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_21,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_377,plain,
% 7.87/1.50      ( ~ v1_funct_1(X3)
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_19,c_23,c_22,c_21]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_378,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | v1_xboole_0(X1)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_377]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_650,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.87/1.50      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.87/1.50      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.87/1.50      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.87/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.87/1.50      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.87/1.50      | ~ v1_funct_1(X0_54)
% 7.87/1.50      | ~ v1_funct_1(X3_54)
% 7.87/1.50      | v1_xboole_0(X1_54)
% 7.87/1.50      | v1_xboole_0(X2_54)
% 7.87/1.50      | v1_xboole_0(X4_54)
% 7.87/1.50      | v1_xboole_0(X5_54)
% 7.87/1.50      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_378]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1568,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.87/1.50      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.87/1.50      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.87/1.50      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.87/1.50      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.87/1.50      | v1_funct_1(X2_54) != iProver_top
% 7.87/1.50      | v1_funct_1(X5_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X3_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X4_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.87/1.50      | ~ v1_xboole_0(X1)
% 7.87/1.50      | v1_xboole_0(X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_683,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.87/1.50      | ~ v1_xboole_0(X1_54)
% 7.87/1.50      | v1_xboole_0(X0_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1538,plain,
% 7.87/1.50      ( m1_subset_1(X0_54,k1_zfmisc_1(X1_54)) != iProver_top
% 7.87/1.50      | v1_xboole_0(X1_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1811,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X4_54) = X5_54
% 7.87/1.50      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.87/1.50      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.87/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.87/1.50      | v1_funct_1(X5_54) != iProver_top
% 7.87/1.50      | v1_funct_1(X2_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X4_54) = iProver_top ),
% 7.87/1.50      inference(forward_subsumption_resolution,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_1568,c_1538]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_9134,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
% 7.87/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.87/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.87/1.50      | v1_funct_1(sK4) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4861,c_1811]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_36,negated_conjecture,
% 7.87/1.50      ( ~ v1_xboole_0(sK1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_39,plain,
% 7.87/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_35,negated_conjecture,
% 7.87/1.50      ( ~ v1_xboole_0(sK2) ),
% 7.87/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_40,plain,
% 7.87/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_45,plain,
% 7.87/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_29,negated_conjecture,
% 7.87/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_46,plain,
% 7.87/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_47,plain,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15212,plain,
% 7.87/1.50      ( v1_funct_1(X1_54) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.87/1.50      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
% 7.87/1.50      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_9134,c_39,c_40,c_45,c_46,c_47]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15213,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),X0_54) = X1_54
% 7.87/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_15212]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15226,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
% 7.87/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.87/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.87/1.50      | v1_funct_1(sK5) != iProver_top
% 7.87/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4855,c_15213]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_33,negated_conjecture,
% 7.87/1.50      ( ~ v1_xboole_0(sK3) ),
% 7.87/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_42,plain,
% 7.87/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_48,plain,
% 7.87/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_26,negated_conjecture,
% 7.87/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_49,plain,
% 7.87/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_50,plain,
% 7.87/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15426,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_15226,c_42,c_48,c_49,c_50]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15436,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2267,c_15426]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_31,negated_conjecture,
% 7.87/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.87/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_658,negated_conjecture,
% 7.87/1.50      ( r1_subset_1(sK2,sK3) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_31]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1560,plain,
% 7.87/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_658]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10,plain,
% 7.87/1.50      ( ~ r1_subset_1(X0,X1)
% 7.87/1.50      | r1_xboole_0(X0,X1)
% 7.87/1.50      | v1_xboole_0(X0)
% 7.87/1.50      | v1_xboole_0(X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_676,plain,
% 7.87/1.50      ( ~ r1_subset_1(X0_54,X1_54)
% 7.87/1.50      | r1_xboole_0(X0_54,X1_54)
% 7.87/1.50      | v1_xboole_0(X1_54)
% 7.87/1.50      | v1_xboole_0(X0_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1543,plain,
% 7.87/1.50      ( r1_subset_1(X0_54,X1_54) != iProver_top
% 7.87/1.50      | r1_xboole_0(X0_54,X1_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4203,plain,
% 7.87/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1560,c_1543]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_44,plain,
% 7.87/1.50      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2018,plain,
% 7.87/1.50      ( ~ r1_subset_1(sK2,sK3)
% 7.87/1.50      | r1_xboole_0(sK2,sK3)
% 7.87/1.50      | v1_xboole_0(sK3)
% 7.87/1.50      | v1_xboole_0(sK2) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_676]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2019,plain,
% 7.87/1.50      ( r1_subset_1(sK2,sK3) != iProver_top
% 7.87/1.50      | r1_xboole_0(sK2,sK3) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK3) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2018]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5061,plain,
% 7.87/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_4203,c_40,c_42,c_44,c_2019]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1,plain,
% 7.87/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_685,plain,
% 7.87/1.50      ( ~ r1_xboole_0(X0_54,X1_54)
% 7.87/1.50      | k3_xboole_0(X0_54,X1_54) = k1_xboole_0 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1536,plain,
% 7.87/1.50      ( k3_xboole_0(X0_54,X1_54) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X0_54,X1_54) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5067,plain,
% 7.87/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5061,c_1536]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_13,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | v1_partfun1(X0,X1)
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | v1_xboole_0(X2) ),
% 7.87/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_673,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.87/1.50      | v1_partfun1(X0_54,X1_54)
% 7.87/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.87/1.50      | ~ v1_funct_1(X0_54)
% 7.87/1.50      | v1_xboole_0(X2_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1546,plain,
% 7.87/1.50      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.87/1.50      | v1_partfun1(X0_54,X1_54) = iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.87/1.50      | v1_funct_1(X0_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X2_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4702,plain,
% 7.87/1.50      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.87/1.50      | v1_partfun1(sK5,sK3) = iProver_top
% 7.87/1.50      | v1_funct_1(sK5) != iProver_top
% 7.87/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1554,c_1546]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2096,plain,
% 7.87/1.50      ( ~ v1_funct_2(sK5,X0_54,X1_54)
% 7.87/1.50      | v1_partfun1(sK5,X0_54)
% 7.87/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.87/1.50      | ~ v1_funct_1(sK5)
% 7.87/1.50      | v1_xboole_0(X1_54) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_673]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2357,plain,
% 7.87/1.50      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.87/1.50      | v1_partfun1(sK5,sK3)
% 7.87/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.87/1.50      | ~ v1_funct_1(sK5)
% 7.87/1.50      | v1_xboole_0(sK1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2096]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2358,plain,
% 7.87/1.50      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.87/1.50      | v1_partfun1(sK5,sK3) = iProver_top
% 7.87/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.87/1.50      | v1_funct_1(sK5) != iProver_top
% 7.87/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2357]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5164,plain,
% 7.87/1.50      ( v1_partfun1(sK5,sK3) = iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_4702,c_39,c_48,c_49,c_50,c_2358]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_16,plain,
% 7.87/1.50      ( ~ v1_partfun1(X0,X1)
% 7.87/1.50      | ~ v4_relat_1(X0,X1)
% 7.87/1.50      | ~ v1_relat_1(X0)
% 7.87/1.50      | k1_relat_1(X0) = X1 ),
% 7.87/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_671,plain,
% 7.87/1.50      ( ~ v1_partfun1(X0_54,X1_54)
% 7.87/1.50      | ~ v4_relat_1(X0_54,X1_54)
% 7.87/1.50      | ~ v1_relat_1(X0_54)
% 7.87/1.50      | k1_relat_1(X0_54) = X1_54 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1548,plain,
% 7.87/1.50      ( k1_relat_1(X0_54) = X1_54
% 7.87/1.50      | v1_partfun1(X0_54,X1_54) != iProver_top
% 7.87/1.50      | v4_relat_1(X0_54,X1_54) != iProver_top
% 7.87/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5169,plain,
% 7.87/1.50      ( k1_relat_1(sK5) = sK3
% 7.87/1.50      | v4_relat_1(sK5,sK3) != iProver_top
% 7.87/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5164,c_1548]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_11,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | v1_relat_1(X0) ),
% 7.87/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_675,plain,
% 7.87/1.50      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.87/1.50      | v1_relat_1(X0_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_11]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1964,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.87/1.50      | v1_relat_1(sK5) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_675]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_12,plain,
% 7.87/1.50      ( v4_relat_1(X0,X1)
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.87/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_674,plain,
% 7.87/1.50      ( v4_relat_1(X0_54,X1_54)
% 7.87/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1996,plain,
% 7.87/1.50      ( v4_relat_1(sK5,sK3)
% 7.87/1.50      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_674]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2189,plain,
% 7.87/1.50      ( ~ v1_partfun1(sK5,X0_54)
% 7.87/1.50      | ~ v4_relat_1(sK5,X0_54)
% 7.87/1.50      | ~ v1_relat_1(sK5)
% 7.87/1.50      | k1_relat_1(sK5) = X0_54 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_671]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2733,plain,
% 7.87/1.50      ( ~ v1_partfun1(sK5,sK3)
% 7.87/1.50      | ~ v4_relat_1(sK5,sK3)
% 7.87/1.50      | ~ v1_relat_1(sK5)
% 7.87/1.50      | k1_relat_1(sK5) = sK3 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2189]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5295,plain,
% 7.87/1.50      ( k1_relat_1(sK5) = sK3 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_5169,c_36,c_27,c_26,c_25,c_1964,c_1996,c_2357,c_2733]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4,plain,
% 7.87/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.87/1.50      | ~ v1_relat_1(X1)
% 7.87/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_682,plain,
% 7.87/1.50      ( ~ r1_xboole_0(X0_54,k1_relat_1(X1_54))
% 7.87/1.50      | ~ v1_relat_1(X1_54)
% 7.87/1.50      | k7_relat_1(X1_54,X0_54) = k1_xboole_0 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_4]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1539,plain,
% 7.87/1.50      ( k7_relat_1(X0_54,X1_54) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X1_54,k1_relat_1(X0_54)) != iProver_top
% 7.87/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5316,plain,
% 7.87/1.50      ( k7_relat_1(sK5,X0_54) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X0_54,sK3) != iProver_top
% 7.87/1.50      | v1_relat_1(sK5) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5295,c_1539]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1965,plain,
% 7.87/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.87/1.50      | v1_relat_1(sK5) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_1964]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5639,plain,
% 7.87/1.50      ( r1_xboole_0(X0_54,sK3) != iProver_top
% 7.87/1.50      | k7_relat_1(sK5,X0_54) = k1_xboole_0 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_5316,c_50,c_1965]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5640,plain,
% 7.87/1.50      ( k7_relat_1(sK5,X0_54) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X0_54,sK3) != iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_5639]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5647,plain,
% 7.87/1.50      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5061,c_5640]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1544,plain,
% 7.87/1.50      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.87/1.50      | v1_relat_1(X0_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2762,plain,
% 7.87/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1554,c_1544]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0)
% 7.87/1.50      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_681,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0_54)
% 7.87/1.50      | k7_relat_1(X0_54,k3_xboole_0(k1_relat_1(X0_54),X1_54)) = k7_relat_1(X0_54,X1_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1540,plain,
% 7.87/1.50      ( k7_relat_1(X0_54,k3_xboole_0(k1_relat_1(X0_54),X1_54)) = k7_relat_1(X0_54,X1_54)
% 7.87/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3578,plain,
% 7.87/1.50      ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_54)) = k7_relat_1(sK5,X0_54) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2762,c_1540]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0)
% 7.87/1.50      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 7.87/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_678,plain,
% 7.87/1.50      ( ~ v1_relat_1(X0_54)
% 7.87/1.50      | k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1541,plain,
% 7.87/1.50      ( k1_relat_1(k7_relat_1(X0_54,X1_54)) = k3_xboole_0(k1_relat_1(X0_54),X1_54)
% 7.87/1.50      | v1_relat_1(X0_54) != iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2841,plain,
% 7.87/1.50      ( k1_relat_1(k7_relat_1(sK5,X0_54)) = k3_xboole_0(k1_relat_1(sK5),X0_54) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2762,c_1541]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3584,plain,
% 7.87/1.50      ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0_54))) = k7_relat_1(sK5,X0_54) ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_3578,c_2841]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5748,plain,
% 7.87/1.50      ( k7_relat_1(sK5,k1_relat_1(k1_xboole_0)) = k7_relat_1(sK5,sK2) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5647,c_3584]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7,plain,
% 7.87/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_679,plain,
% 7.87/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5749,plain,
% 7.87/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_5748,c_679,c_5647]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15437,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(light_normalisation,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_15436,c_5067,c_5749]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4703,plain,
% 7.87/1.50      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.87/1.50      | v1_partfun1(sK4,sK2) = iProver_top
% 7.87/1.50      | v1_funct_1(sK4) != iProver_top
% 7.87/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1557,c_1546]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2101,plain,
% 7.87/1.50      ( ~ v1_funct_2(sK4,X0_54,X1_54)
% 7.87/1.50      | v1_partfun1(sK4,X0_54)
% 7.87/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 7.87/1.50      | ~ v1_funct_1(sK4)
% 7.87/1.50      | v1_xboole_0(X1_54) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_673]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2360,plain,
% 7.87/1.50      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.87/1.50      | v1_partfun1(sK4,sK2)
% 7.87/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.87/1.50      | ~ v1_funct_1(sK4)
% 7.87/1.50      | v1_xboole_0(sK1) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2101]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2361,plain,
% 7.87/1.50      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.87/1.50      | v1_partfun1(sK4,sK2) = iProver_top
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.87/1.50      | v1_funct_1(sK4) != iProver_top
% 7.87/1.50      | v1_xboole_0(sK1) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_2360]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5172,plain,
% 7.87/1.50      ( v1_partfun1(sK4,sK2) = iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_4703,c_39,c_45,c_46,c_47,c_2361]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5177,plain,
% 7.87/1.50      ( k1_relat_1(sK4) = sK2
% 7.87/1.50      | v4_relat_1(sK4,sK2) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5172,c_1548]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1967,plain,
% 7.87/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.87/1.50      | v1_relat_1(sK4) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_675]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1999,plain,
% 7.87/1.50      ( v4_relat_1(sK4,sK2)
% 7.87/1.50      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_674]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2223,plain,
% 7.87/1.50      ( ~ v1_partfun1(sK4,X0_54)
% 7.87/1.50      | ~ v4_relat_1(sK4,X0_54)
% 7.87/1.50      | ~ v1_relat_1(sK4)
% 7.87/1.50      | k1_relat_1(sK4) = X0_54 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_671]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2235,plain,
% 7.87/1.50      ( ~ v1_partfun1(sK4,sK2)
% 7.87/1.50      | ~ v4_relat_1(sK4,sK2)
% 7.87/1.50      | ~ v1_relat_1(sK4)
% 7.87/1.50      | k1_relat_1(sK4) = sK2 ),
% 7.87/1.50      inference(instantiation,[status(thm)],[c_2223]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5428,plain,
% 7.87/1.50      ( k1_relat_1(sK4) = sK2 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_5177,c_36,c_30,c_29,c_28,c_1967,c_1999,c_2235,c_2360]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2763,plain,
% 7.87/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_1557,c_1544]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2845,plain,
% 7.87/1.50      ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(k1_relat_1(sK4),X0_54) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2763,c_1541]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5433,plain,
% 7.87/1.50      ( k1_relat_1(k7_relat_1(sK4,X0_54)) = k3_xboole_0(sK2,X0_54) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_5428,c_2845]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3579,plain,
% 7.87/1.50      ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_54)) = k7_relat_1(sK4,X0_54) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2763,c_1540]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_3581,plain,
% 7.87/1.50      ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0_54))) = k7_relat_1(sK4,X0_54) ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_3579,c_2845]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6303,plain,
% 7.87/1.50      ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_54)) = k7_relat_1(sK4,X0_54) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_5433,c_3581]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15438,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | k7_relat_1(sK4,sK3) != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_15437,c_2267,c_6303]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5300,plain,
% 7.87/1.50      ( k1_relat_1(k7_relat_1(sK5,X0_54)) = k3_xboole_0(sK3,X0_54) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_5295,c_2841]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6036,plain,
% 7.87/1.50      ( k3_xboole_0(sK3,sK2) = k1_relat_1(k1_xboole_0) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5647,c_5300]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6057,plain,
% 7.87/1.50      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_6036,c_679]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_0,plain,
% 7.87/1.50      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.87/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_686,plain,
% 7.87/1.50      ( r1_xboole_0(X0_54,X1_54)
% 7.87/1.50      | k3_xboole_0(X0_54,X1_54) != k1_xboole_0 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_0]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1535,plain,
% 7.87/1.50      ( k3_xboole_0(X0_54,X1_54) != k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X0_54,X1_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6369,plain,
% 7.87/1.50      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_6057,c_1535]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5449,plain,
% 7.87/1.50      ( k7_relat_1(sK4,X0_54) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X0_54,sK2) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5428,c_1539]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1968,plain,
% 7.87/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.87/1.50      | v1_relat_1(sK4) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_1967]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5649,plain,
% 7.87/1.50      ( r1_xboole_0(X0_54,sK2) != iProver_top
% 7.87/1.50      | k7_relat_1(sK4,X0_54) = k1_xboole_0 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_5449,c_47,c_1968]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5650,plain,
% 7.87/1.50      ( k7_relat_1(sK4,X0_54) = k1_xboole_0
% 7.87/1.50      | r1_xboole_0(X0_54,sK2) != iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_5649]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6754,plain,
% 7.87/1.50      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_6369,c_5650]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15439,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_15438,c_6754]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_15440,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(equality_resolution_simp,[status(thm)],[c_15439]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_20,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.87/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_368,plain,
% 7.87/1.50      ( ~ v1_funct_1(X3)
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X1)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_20,c_23,c_22,c_21]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_369,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.87/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.87/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.87/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.87/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.87/1.50      | ~ v1_funct_1(X0)
% 7.87/1.50      | ~ v1_funct_1(X3)
% 7.87/1.50      | v1_xboole_0(X1)
% 7.87/1.50      | v1_xboole_0(X2)
% 7.87/1.50      | v1_xboole_0(X4)
% 7.87/1.50      | v1_xboole_0(X5)
% 7.87/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_368]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_651,plain,
% 7.87/1.50      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.87/1.50      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.87/1.50      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.87/1.50      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.87/1.50      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.87/1.50      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.87/1.50      | ~ v1_funct_1(X0_54)
% 7.87/1.50      | ~ v1_funct_1(X3_54)
% 7.87/1.50      | v1_xboole_0(X1_54)
% 7.87/1.50      | v1_xboole_0(X2_54)
% 7.87/1.50      | v1_xboole_0(X4_54)
% 7.87/1.50      | v1_xboole_0(X5_54)
% 7.87/1.50      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_369]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1567,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.87/1.50      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.87/1.50      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.87/1.50      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.87/1.50      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.87/1.50      | v1_funct_1(X2_54) != iProver_top
% 7.87/1.50      | v1_funct_1(X5_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X3_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X4_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_651]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_1783,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X0_54,X4_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X0_54,X4_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X3_54,X0_54,X4_54),X1_54,k1_tmap_1(X3_54,X1_54,X0_54,X4_54,X2_54,X5_54),X0_54) = X2_54
% 7.87/1.50      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.87/1.50      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.87/1.50      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.87/1.50      | v1_funct_1(X5_54) != iProver_top
% 7.87/1.50      | v1_funct_1(X2_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X1_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(X4_54) = iProver_top ),
% 7.87/1.50      inference(forward_subsumption_resolution,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_1567,c_1538]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_7219,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
% 7.87/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.87/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.87/1.50      | v1_funct_1(sK4) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.87/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4861,c_1783]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8985,plain,
% 7.87/1.50      ( v1_funct_1(X1_54) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.87/1.50      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
% 7.87/1.50      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_7219,c_39,c_40,c_45,c_46,c_47]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8986,plain,
% 7.87/1.50      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,sK2,X0_54)) != k7_relat_1(sK4,k9_subset_1(X2_54,sK2,X0_54))
% 7.87/1.50      | k2_partfun1(k4_subset_1(X2_54,sK2,X0_54),sK1,k1_tmap_1(X2_54,sK1,sK2,X0_54,sK4,X1_54),sK2) = sK4
% 7.87/1.50      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.87/1.50      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X2_54)) != iProver_top
% 7.87/1.50      | v1_funct_1(X1_54) != iProver_top
% 7.87/1.50      | v1_xboole_0(X0_54) = iProver_top ),
% 7.87/1.50      inference(renaming,[status(thm)],[c_8985]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_8999,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
% 7.87/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.87/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.87/1.50      | v1_funct_1(sK5) != iProver_top
% 7.87/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_4855,c_8986]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10274,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3))
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.87/1.50      inference(global_propositional_subsumption,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_8999,c_42,c_48,c_49,c_50]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10284,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_2267,c_10274]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10285,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(light_normalisation,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_10284,c_5067,c_5749]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10286,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | k7_relat_1(sK4,sK3) != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_10285,c_2267,c_6303]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10287,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | k1_xboole_0 != k1_xboole_0
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_10286,c_6754]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_10288,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.87/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.87/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.87/1.50      inference(equality_resolution_simp,[status(thm)],[c_10287]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6470,plain,
% 7.87/1.50      ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
% 7.87/1.50      inference(superposition,[status(thm)],[c_5067,c_6303]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6957,plain,
% 7.87/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_6754,c_6470]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_24,negated_conjecture,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.87/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_665,negated_conjecture,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.87/1.50      inference(subtyping,[status(esa)],[c_24]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_2479,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_2267,c_665]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_4859,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_4855,c_2479]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5056,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_4859,c_4861]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_5292,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.87/1.50      inference(demodulation,[status(thm)],[c_5067,c_5056]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_6326,plain,
% 7.87/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.87/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.87/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.87/1.50      inference(light_normalisation,[status(thm)],[c_5292,c_5749]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_43,plain,
% 7.87/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_34,negated_conjecture,
% 7.87/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.87/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(c_41,plain,
% 7.87/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.87/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.87/1.50  
% 7.87/1.50  cnf(contradiction,plain,
% 7.87/1.50      ( $false ),
% 7.87/1.50      inference(minisat,
% 7.87/1.50                [status(thm)],
% 7.87/1.50                [c_15440,c_10288,c_6957,c_6326,c_43,c_41]) ).
% 7.87/1.50  
% 7.87/1.50  
% 7.87/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.50  
% 7.87/1.50  ------                               Statistics
% 7.87/1.50  
% 7.87/1.50  ------ Selected
% 7.87/1.50  
% 7.87/1.50  total_time:                             0.696
% 7.87/1.50  
%------------------------------------------------------------------------------
