%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:40 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  249 (3663 expanded)
%              Number of clauses        :  167 (1110 expanded)
%              Number of leaves         :   22 (1289 expanded)
%              Depth                    :   24
%              Number of atoms          : 1172 (40163 expanded)
%              Number of equality atoms :  458 (9324 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   3 average)
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
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f47,f46,f45,f44,f43,f42])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f33])).

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

fof(f65,plain,(
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

fof(f86,plain,(
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
    inference(equality_resolution,[],[f65])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f67,plain,(
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

fof(f68,plain,(
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

fof(f69,plain,(
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

fof(f71,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f74,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
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

fof(f87,plain,(
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
    inference(equality_resolution,[],[f64])).

fof(f83,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f70,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_382,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1206,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_404,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1185,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_404])).

cnf(c_2066,plain,
    ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1206,c_1185])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_386,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1202,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1194,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_5430,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1194])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_1976,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_5921,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5430,c_27,c_25,c_1976])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_389,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1199,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_389])).

cnf(c_5429,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1194])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1703,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_1945,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_5861,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5429,c_24,c_22,c_1945])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f67])).

cnf(c_19,plain,
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
    inference(cnf_transformation,[],[f68])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f69])).

cnf(c_350,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_20,c_19,c_18])).

cnf(c_351,plain,
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
    inference(renaming,[status(thm)],[c_350])).

cnf(c_375,plain,
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
    inference(subtyping,[status(esa)],[c_351])).

cnf(c_1213,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_11742,plain,
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
    inference(superposition,[status(thm)],[c_5861,c_1213])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14285,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11742,c_36,c_39,c_45,c_46,c_47])).

cnf(c_14286,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_14285])).

cnf(c_14301,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5921,c_14286])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14347,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14301,c_37,c_42,c_43,c_44])).

cnf(c_14348,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_14347])).

cnf(c_14358,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_14348])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_383,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1205,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_12,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_397,plain,
    ( ~ r1_subset_1(X0_51,X1_51)
    | r1_xboole_0(X0_51,X1_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1192,plain,
    ( r1_subset_1(X0_51,X1_51) != iProver_top
    | r1_xboole_0(X0_51,X1_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_3989,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1192])).

cnf(c_41,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1634,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_397])).

cnf(c_1635,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_4643,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3989,c_37,c_39,c_41,c_1635])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_407,plain,
    ( ~ r1_xboole_0(X0_51,X1_51)
    | k3_xboole_0(X0_51,X1_51) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1183,plain,
    ( k3_xboole_0(X0_51,X1_51) = k1_xboole_0
    | r1_xboole_0(X0_51,X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_4650,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4643,c_1183])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_403,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1186,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_2293,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1186])).

cnf(c_2164,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_403,c_389])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_402,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_2226,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2164,c_402])).

cnf(c_2227,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2226])).

cnf(c_2743,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2293,c_2227])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_406,plain,
    ( ~ r1_xboole_0(X0_51,X1_51)
    | r1_xboole_0(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1184,plain,
    ( r1_xboole_0(X0_51,X1_51) != iProver_top
    | r1_xboole_0(X1_51,X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_4649,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4643,c_1184])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_400,plain,
    ( ~ r1_xboole_0(X0_51,X1_51)
    | ~ v1_relat_1(X2_51)
    | k7_relat_1(k7_relat_1(X2_51,X0_51),X1_51) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1189,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
    | r1_xboole_0(X1_51,X2_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_5619,plain,
    ( k7_relat_1(k7_relat_1(X0_51,sK3),sK2) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_4649,c_1189])).

cnf(c_8877,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK3),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2743,c_5619])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_396,plain,
    ( v4_relat_1(X0_51,X1_51)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1193,plain,
    ( v4_relat_1(X0_51,X1_51) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_396])).

cnf(c_3174,plain,
    ( v4_relat_1(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1193])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_399,plain,
    ( ~ v4_relat_1(X0_51,X1_51)
    | ~ v1_relat_1(X0_51)
    | k7_relat_1(X0_51,X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1190,plain,
    ( k7_relat_1(X0_51,X1_51) = X0_51
    | v4_relat_1(X0_51,X1_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_3413,plain,
    ( k7_relat_1(sK5,sK3) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3174,c_1190])).

cnf(c_1628,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_1827,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK3) = sK5 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_3543,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3413,c_22,c_1628,c_1827,c_2226])).

cnf(c_8883,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8877,c_3543])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_409,plain,
    ( k3_xboole_0(X0_51,X1_51) = k3_xboole_0(X1_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_401,plain,
    ( ~ v1_relat_1(X0_51)
    | k3_xboole_0(k7_relat_1(X0_51,X1_51),k7_relat_1(X0_51,X2_51)) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1188,plain,
    ( k3_xboole_0(k7_relat_1(X0_51,X1_51),k7_relat_1(X0_51,X2_51)) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51))
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_3400,plain,
    ( k3_xboole_0(k7_relat_1(sK5,X0_51),k7_relat_1(sK5,X1_51)) = k7_relat_1(sK5,k3_xboole_0(X0_51,X1_51)) ),
    inference(superposition,[status(thm)],[c_2743,c_1188])).

cnf(c_3644,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK3,X0_51)) = k3_xboole_0(sK5,k7_relat_1(sK5,X0_51)) ),
    inference(superposition,[status(thm)],[c_3543,c_3400])).

cnf(c_3756,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_51,sK3)) = k3_xboole_0(sK5,k7_relat_1(sK5,X0_51)) ),
    inference(superposition,[status(thm)],[c_409,c_3644])).

cnf(c_4772,plain,
    ( k3_xboole_0(sK5,k7_relat_1(sK5,sK2)) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4650,c_3756])).

cnf(c_9164,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k3_xboole_0(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8883,c_4772])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_405,plain,
    ( k3_xboole_0(X0_51,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_9166,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9164,c_405])).

cnf(c_14359,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14358,c_4650,c_9166])).

cnf(c_3175,plain,
    ( v4_relat_1(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1193])).

cnf(c_3540,plain,
    ( k7_relat_1(sK4,sK2) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3175,c_1190])).

cnf(c_1631,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_396])).

cnf(c_1830,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_2166,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_403,c_386])).

cnf(c_2233,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2166,c_402])).

cnf(c_3638,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3540,c_25,c_1631,c_1830,c_2233])).

cnf(c_2294,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1186])).

cnf(c_2234,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2868,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2294,c_2234])).

cnf(c_3401,plain,
    ( k3_xboole_0(k7_relat_1(sK4,X0_51),k7_relat_1(sK4,X1_51)) = k7_relat_1(sK4,k3_xboole_0(X0_51,X1_51)) ),
    inference(superposition,[status(thm)],[c_2868,c_1188])).

cnf(c_3728,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_51)) = k3_xboole_0(sK4,k7_relat_1(sK4,X0_51)) ),
    inference(superposition,[status(thm)],[c_3638,c_3401])).

cnf(c_14360,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k3_xboole_0(sK4,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14359,c_2066,c_3728])).

cnf(c_5617,plain,
    ( k7_relat_1(k7_relat_1(X0_51,sK2),sK3) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_4643,c_1189])).

cnf(c_5930,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2868,c_5617])).

cnf(c_5932,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5930,c_3638])).

cnf(c_14361,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k3_xboole_0(sK4,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14360,c_5932])).

cnf(c_14362,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14361,c_405])).

cnf(c_14363,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14362])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_341,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_20,c_19,c_18])).

cnf(c_342,plain,
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
    inference(renaming,[status(thm)],[c_341])).

cnf(c_376,plain,
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
    inference(subtyping,[status(esa)],[c_342])).

cnf(c_1212,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_9884,plain,
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
    inference(superposition,[status(thm)],[c_5861,c_1212])).

cnf(c_10578,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9884,c_36,c_39,c_45,c_46,c_47])).

cnf(c_10579,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_10578])).

cnf(c_10594,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5921,c_10579])).

cnf(c_10757,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10594,c_37,c_42,c_43,c_44])).

cnf(c_10758,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_10757])).

cnf(c_10768,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_10758])).

cnf(c_10769,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10768,c_4650,c_9166])).

cnf(c_10770,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k3_xboole_0(sK4,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10769,c_2066,c_3728])).

cnf(c_10771,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k3_xboole_0(sK4,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10770,c_5932])).

cnf(c_10772,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10771,c_405])).

cnf(c_10773,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10772])).

cnf(c_5327,plain,
    ( k3_xboole_0(sK4,k7_relat_1(sK4,sK3)) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4650,c_3728])).

cnf(c_6200,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k3_xboole_0(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5932,c_5327])).

cnf(c_6201,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6200,c_405])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_390,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2216,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2066,c_390])).

cnf(c_4769,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4650,c_2216])).

cnf(c_5865,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5861,c_4769])).

cnf(c_6045,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5865,c_5921])).

cnf(c_6612,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6201,c_6045])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_35,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14363,c_10773,c_9166,c_6612,c_40,c_38,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.58/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.50  
% 7.58/1.50  ------  iProver source info
% 7.58/1.50  
% 7.58/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.50  git: non_committed_changes: false
% 7.58/1.50  git: last_make_outside_of_git: false
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  ------ Parsing...
% 7.58/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.50  ------ Proving...
% 7.58/1.50  ------ Problem Properties 
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  clauses                                 35
% 7.58/1.50  conjectures                             14
% 7.58/1.50  EPR                                     12
% 7.58/1.50  Horn                                    27
% 7.58/1.50  unary                                   16
% 7.58/1.50  binary                                  6
% 7.58/1.50  lits                                    135
% 7.58/1.50  lits eq                                 18
% 7.58/1.50  fd_pure                                 0
% 7.58/1.50  fd_pseudo                               0
% 7.58/1.50  fd_cond                                 0
% 7.58/1.50  fd_pseudo_cond                          0
% 7.58/1.50  AC symbols                              0
% 7.58/1.50  
% 7.58/1.50  ------ Input Options Time Limit: Unbounded
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  Current options:
% 7.58/1.50  ------ 
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ Proving...
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS status Theorem for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  fof(f16,conjecture,(
% 7.58/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f17,negated_conjecture,(
% 7.58/1.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.58/1.50    inference(negated_conjecture,[],[f16])).
% 7.58/1.50  
% 7.58/1.50  fof(f36,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f17])).
% 7.58/1.50  
% 7.58/1.50  fof(f37,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f36])).
% 7.58/1.50  
% 7.58/1.50  fof(f47,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f46,plain,(
% 7.58/1.50    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f45,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f44,plain,(
% 7.58/1.50    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f43,plain,(
% 7.58/1.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f42,plain,(
% 7.58/1.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f48,plain,(
% 7.58/1.50    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.58/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f37,f47,f46,f45,f44,f43,f42])).
% 7.58/1.50  
% 7.58/1.50  fof(f75,plain,(
% 7.58/1.50    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f5,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f20,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f5])).
% 7.58/1.50  
% 7.58/1.50  fof(f54,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f20])).
% 7.58/1.50  
% 7.58/1.50  fof(f79,plain,(
% 7.58/1.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f13,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f30,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.58/1.50    inference(ennf_transformation,[],[f13])).
% 7.58/1.50  
% 7.58/1.50  fof(f31,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.58/1.50    inference(flattening,[],[f30])).
% 7.58/1.50  
% 7.58/1.50  fof(f63,plain,(
% 7.58/1.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f31])).
% 7.58/1.50  
% 7.58/1.50  fof(f77,plain,(
% 7.58/1.50    v1_funct_1(sK4)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f82,plain,(
% 7.58/1.50    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f80,plain,(
% 7.58/1.50    v1_funct_1(sK5)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f14,axiom,(
% 7.58/1.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f32,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f14])).
% 7.58/1.50  
% 7.58/1.50  fof(f33,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f32])).
% 7.58/1.50  
% 7.58/1.50  fof(f40,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(nnf_transformation,[],[f33])).
% 7.58/1.50  
% 7.58/1.50  fof(f41,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f40])).
% 7.58/1.50  
% 7.58/1.50  fof(f65,plain,(
% 7.58/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f41])).
% 7.58/1.50  
% 7.58/1.50  fof(f86,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(equality_resolution,[],[f65])).
% 7.58/1.50  
% 7.58/1.50  fof(f15,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f34,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f15])).
% 7.58/1.50  
% 7.58/1.50  fof(f35,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f34])).
% 7.58/1.50  
% 7.58/1.50  fof(f67,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f68,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f69,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f71,plain,(
% 7.58/1.50    ~v1_xboole_0(sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f74,plain,(
% 7.58/1.50    ~v1_xboole_0(sK3)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f81,plain,(
% 7.58/1.50    v1_funct_2(sK5,sK3,sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f72,plain,(
% 7.58/1.50    ~v1_xboole_0(sK2)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f78,plain,(
% 7.58/1.50    v1_funct_2(sK4,sK2,sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f76,plain,(
% 7.58/1.50    r1_subset_1(sK2,sK3)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f11,axiom,(
% 7.58/1.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f27,plain,(
% 7.58/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f11])).
% 7.58/1.50  
% 7.58/1.50  fof(f28,plain,(
% 7.58/1.50    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.58/1.50    inference(flattening,[],[f27])).
% 7.58/1.50  
% 7.58/1.50  fof(f39,plain,(
% 7.58/1.50    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.58/1.50    inference(nnf_transformation,[],[f28])).
% 7.58/1.50  
% 7.58/1.50  fof(f60,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f39])).
% 7.58/1.50  
% 7.58/1.50  fof(f2,axiom,(
% 7.58/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f38,plain,(
% 7.58/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.58/1.50    inference(nnf_transformation,[],[f2])).
% 7.58/1.50  
% 7.58/1.50  fof(f50,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f38])).
% 7.58/1.50  
% 7.58/1.50  fof(f6,axiom,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f21,plain,(
% 7.58/1.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f6])).
% 7.58/1.50  
% 7.58/1.50  fof(f55,plain,(
% 7.58/1.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f21])).
% 7.58/1.50  
% 7.58/1.50  fof(f7,axiom,(
% 7.58/1.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f56,plain,(
% 7.58/1.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f7])).
% 7.58/1.50  
% 7.58/1.50  fof(f3,axiom,(
% 7.58/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f19,plain,(
% 7.58/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.58/1.50    inference(ennf_transformation,[],[f3])).
% 7.58/1.50  
% 7.58/1.50  fof(f52,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f19])).
% 7.58/1.50  
% 7.58/1.50  fof(f9,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f23,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.58/1.50    inference(ennf_transformation,[],[f9])).
% 7.58/1.50  
% 7.58/1.50  fof(f24,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.58/1.50    inference(flattening,[],[f23])).
% 7.58/1.50  
% 7.58/1.50  fof(f58,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f24])).
% 7.58/1.50  
% 7.58/1.50  fof(f12,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f18,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.58/1.50    inference(pure_predicate_removal,[],[f12])).
% 7.58/1.50  
% 7.58/1.50  fof(f29,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f18])).
% 7.58/1.50  
% 7.58/1.50  fof(f62,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f29])).
% 7.58/1.50  
% 7.58/1.50  fof(f10,axiom,(
% 7.58/1.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f25,plain,(
% 7.58/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f10])).
% 7.58/1.50  
% 7.58/1.50  fof(f26,plain,(
% 7.58/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(flattening,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f59,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f26])).
% 7.58/1.50  
% 7.58/1.50  fof(f1,axiom,(
% 7.58/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f49,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f1])).
% 7.58/1.50  
% 7.58/1.50  fof(f8,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f22,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.58/1.50    inference(ennf_transformation,[],[f8])).
% 7.58/1.50  
% 7.58/1.50  fof(f57,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f22])).
% 7.58/1.50  
% 7.58/1.50  fof(f4,axiom,(
% 7.58/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f53,plain,(
% 7.58/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.58/1.50    inference(cnf_transformation,[],[f4])).
% 7.58/1.50  
% 7.58/1.50  fof(f64,plain,(
% 7.58/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f41])).
% 7.58/1.50  
% 7.58/1.50  fof(f87,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.58/1.50    inference(equality_resolution,[],[f64])).
% 7.58/1.50  
% 7.58/1.50  fof(f83,plain,(
% 7.58/1.50    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f73,plain,(
% 7.58/1.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f70,plain,(
% 7.58/1.50    ~v1_xboole_0(sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  cnf(c_29,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_382,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_29]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1206,plain,
% 7.58/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_404,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 7.58/1.50      | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1185,plain,
% 7.58/1.50      ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
% 7.58/1.50      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_404]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2066,plain,
% 7.58/1.50      ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1206,c_1185]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_386,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_25]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1202,plain,
% 7.58/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.58/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_395,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.58/1.50      | ~ v1_funct_1(X0_51)
% 7.58/1.50      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 7.58/1.50      inference(subtyping,[status(esa)],[c_14]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1194,plain,
% 7.58/1.50      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 7.58/1.50      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2_51) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5430,plain,
% 7.58/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 7.58/1.50      | v1_funct_1(sK4) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_1202,c_1194]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_27,negated_conjecture,
% 7.58/1.50      ( v1_funct_1(sK4) ),
% 7.58/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1708,plain,
% 7.58/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.58/1.51      | ~ v1_funct_1(sK4)
% 7.58/1.51      | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_395]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1976,plain,
% 7.58/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.58/1.51      | ~ v1_funct_1(sK4)
% 7.58/1.51      | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_1708]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5921,plain,
% 7.58/1.51      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_5430,c_27,c_25,c_1976]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_22,negated_conjecture,
% 7.58/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.58/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_389,negated_conjecture,
% 7.58/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_22]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1199,plain,
% 7.58/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_389]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5429,plain,
% 7.58/1.51      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
% 7.58/1.51      | v1_funct_1(sK5) != iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_1199,c_1194]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_24,negated_conjecture,
% 7.58/1.51      ( v1_funct_1(sK5) ),
% 7.58/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1703,plain,
% 7.58/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.58/1.51      | ~ v1_funct_1(sK5)
% 7.58/1.51      | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_395]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1945,plain,
% 7.58/1.51      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.58/1.51      | ~ v1_funct_1(sK5)
% 7.58/1.51      | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_1703]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5861,plain,
% 7.58/1.51      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_5429,c_24,c_22,c_1945]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_16,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1)
% 7.58/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.58/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_20,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_19,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_18,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_350,plain,
% 7.58/1.51      ( ~ v1_funct_1(X3)
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1)
% 7.58/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_16,c_20,c_19,c_18]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_351,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | v1_xboole_0(X1)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.58/1.51      inference(renaming,[status(thm)],[c_350]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_375,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.58/1.51      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.58/1.51      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.58/1.51      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.58/1.51      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.58/1.51      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.58/1.51      | ~ v1_funct_1(X0_51)
% 7.58/1.51      | ~ v1_funct_1(X3_51)
% 7.58/1.51      | v1_xboole_0(X1_51)
% 7.58/1.51      | v1_xboole_0(X2_51)
% 7.58/1.51      | v1_xboole_0(X4_51)
% 7.58/1.51      | v1_xboole_0(X5_51)
% 7.58/1.51      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_351]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1213,plain,
% 7.58/1.51      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
% 7.58/1.51      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 7.58/1.51      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 7.58/1.51      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.58/1.51      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 7.58/1.51      | v1_funct_1(X2_51) != iProver_top
% 7.58/1.51      | v1_funct_1(X5_51) != iProver_top
% 7.58/1.51      | v1_xboole_0(X3_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X1_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X4_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_11742,plain,
% 7.58/1.51      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.58/1.51      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.58/1.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | v1_funct_1(X1_51) != iProver_top
% 7.58/1.51      | v1_funct_1(sK5) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X2_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK1) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_5861,c_1213]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_33,negated_conjecture,
% 7.58/1.51      ( ~ v1_xboole_0(sK1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_36,plain,
% 7.58/1.51      ( v1_xboole_0(sK1) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_30,negated_conjecture,
% 7.58/1.51      ( ~ v1_xboole_0(sK3) ),
% 7.58/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_39,plain,
% 7.58/1.51      ( v1_xboole_0(sK3) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_45,plain,
% 7.58/1.51      ( v1_funct_1(sK5) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_23,negated_conjecture,
% 7.58/1.51      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_46,plain,
% 7.58/1.51      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_47,plain,
% 7.58/1.51      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14285,plain,
% 7.58/1.51      ( v1_funct_1(X1_51) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.58/1.51      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.58/1.51      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X2_51) = iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_11742,c_36,c_39,c_45,c_46,c_47]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14286,plain,
% 7.58/1.51      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.58/1.51      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | v1_funct_1(X1_51) != iProver_top
% 7.58/1.51      | v1_xboole_0(X2_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(renaming,[status(thm)],[c_14285]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14301,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.58/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | v1_funct_1(sK4) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_5921,c_14286]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_32,negated_conjecture,
% 7.58/1.51      ( ~ v1_xboole_0(sK2) ),
% 7.58/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_37,plain,
% 7.58/1.51      ( v1_xboole_0(sK2) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_42,plain,
% 7.58/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_26,negated_conjecture,
% 7.58/1.51      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_43,plain,
% 7.58/1.51      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_44,plain,
% 7.58/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14347,plain,
% 7.58/1.51      ( v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_14301,c_37,c_42,c_43,c_44]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14348,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(renaming,[status(thm)],[c_14347]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14358,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_2066,c_14348]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_28,negated_conjecture,
% 7.58/1.51      ( r1_subset_1(sK2,sK3) ),
% 7.58/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_383,negated_conjecture,
% 7.58/1.51      ( r1_subset_1(sK2,sK3) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_28]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1205,plain,
% 7.58/1.51      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_12,plain,
% 7.58/1.51      ( ~ r1_subset_1(X0,X1)
% 7.58/1.51      | r1_xboole_0(X0,X1)
% 7.58/1.51      | v1_xboole_0(X0)
% 7.58/1.51      | v1_xboole_0(X1) ),
% 7.58/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_397,plain,
% 7.58/1.51      ( ~ r1_subset_1(X0_51,X1_51)
% 7.58/1.51      | r1_xboole_0(X0_51,X1_51)
% 7.58/1.51      | v1_xboole_0(X1_51)
% 7.58/1.51      | v1_xboole_0(X0_51) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_12]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1192,plain,
% 7.58/1.51      ( r1_subset_1(X0_51,X1_51) != iProver_top
% 7.58/1.51      | r1_xboole_0(X0_51,X1_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X1_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3989,plain,
% 7.58/1.51      ( r1_xboole_0(sK2,sK3) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK3) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_1205,c_1192]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_41,plain,
% 7.58/1.51      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1634,plain,
% 7.58/1.51      ( ~ r1_subset_1(sK2,sK3)
% 7.58/1.51      | r1_xboole_0(sK2,sK3)
% 7.58/1.51      | v1_xboole_0(sK3)
% 7.58/1.51      | v1_xboole_0(sK2) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_397]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1635,plain,
% 7.58/1.51      ( r1_subset_1(sK2,sK3) != iProver_top
% 7.58/1.51      | r1_xboole_0(sK2,sK3) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK3) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_4643,plain,
% 7.58/1.51      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_3989,c_37,c_39,c_41,c_1635]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2,plain,
% 7.58/1.51      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.58/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_407,plain,
% 7.58/1.51      ( ~ r1_xboole_0(X0_51,X1_51)
% 7.58/1.51      | k3_xboole_0(X0_51,X1_51) = k1_xboole_0 ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1183,plain,
% 7.58/1.51      ( k3_xboole_0(X0_51,X1_51) = k1_xboole_0
% 7.58/1.51      | r1_xboole_0(X0_51,X1_51) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_4650,plain,
% 7.58/1.51      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_4643,c_1183]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_6,plain,
% 7.58/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.58/1.51      | ~ v1_relat_1(X1)
% 7.58/1.51      | v1_relat_1(X0) ),
% 7.58/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_403,plain,
% 7.58/1.51      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 7.58/1.51      | ~ v1_relat_1(X1_51)
% 7.58/1.51      | v1_relat_1(X0_51) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1186,plain,
% 7.58/1.51      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 7.58/1.51      | v1_relat_1(X1_51) != iProver_top
% 7.58/1.51      | v1_relat_1(X0_51) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2293,plain,
% 7.58/1.51      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.58/1.51      | v1_relat_1(sK5) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_1199,c_1186]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2164,plain,
% 7.58/1.51      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1)) | v1_relat_1(sK5) ),
% 7.58/1.51      inference(resolution,[status(thm)],[c_403,c_389]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_7,plain,
% 7.58/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.58/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_402,plain,
% 7.58/1.51      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_7]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2226,plain,
% 7.58/1.51      ( v1_relat_1(sK5) ),
% 7.58/1.51      inference(forward_subsumption_resolution,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_2164,c_402]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2227,plain,
% 7.58/1.51      ( v1_relat_1(sK5) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_2226]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2743,plain,
% 7.58/1.51      ( v1_relat_1(sK5) = iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_2293,c_2227]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3,plain,
% 7.58/1.51      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.58/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_406,plain,
% 7.58/1.51      ( ~ r1_xboole_0(X0_51,X1_51) | r1_xboole_0(X1_51,X0_51) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1184,plain,
% 7.58/1.51      ( r1_xboole_0(X0_51,X1_51) != iProver_top
% 7.58/1.51      | r1_xboole_0(X1_51,X0_51) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_4649,plain,
% 7.58/1.51      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_4643,c_1184]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_9,plain,
% 7.58/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.58/1.51      | ~ v1_relat_1(X2)
% 7.58/1.51      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.58/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_400,plain,
% 7.58/1.51      ( ~ r1_xboole_0(X0_51,X1_51)
% 7.58/1.51      | ~ v1_relat_1(X2_51)
% 7.58/1.51      | k7_relat_1(k7_relat_1(X2_51,X0_51),X1_51) = k1_xboole_0 ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1189,plain,
% 7.58/1.51      ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
% 7.58/1.51      | r1_xboole_0(X1_51,X2_51) != iProver_top
% 7.58/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5619,plain,
% 7.58/1.51      ( k7_relat_1(k7_relat_1(X0_51,sK3),sK2) = k1_xboole_0
% 7.58/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_4649,c_1189]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_8877,plain,
% 7.58/1.51      ( k7_relat_1(k7_relat_1(sK5,sK3),sK2) = k1_xboole_0 ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_2743,c_5619]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_13,plain,
% 7.58/1.51      ( v4_relat_1(X0,X1)
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.58/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_396,plain,
% 7.58/1.51      ( v4_relat_1(X0_51,X1_51)
% 7.58/1.51      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_13]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1193,plain,
% 7.58/1.51      ( v4_relat_1(X0_51,X1_51) = iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_396]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3174,plain,
% 7.58/1.51      ( v4_relat_1(sK5,sK3) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_1199,c_1193]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10,plain,
% 7.58/1.51      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.58/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_399,plain,
% 7.58/1.51      ( ~ v4_relat_1(X0_51,X1_51)
% 7.58/1.51      | ~ v1_relat_1(X0_51)
% 7.58/1.51      | k7_relat_1(X0_51,X1_51) = X0_51 ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_10]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1190,plain,
% 7.58/1.51      ( k7_relat_1(X0_51,X1_51) = X0_51
% 7.58/1.51      | v4_relat_1(X0_51,X1_51) != iProver_top
% 7.58/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3413,plain,
% 7.58/1.51      ( k7_relat_1(sK5,sK3) = sK5 | v1_relat_1(sK5) != iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_3174,c_1190]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1628,plain,
% 7.58/1.51      ( v4_relat_1(sK5,sK3)
% 7.58/1.51      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_396]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1827,plain,
% 7.58/1.51      ( ~ v4_relat_1(sK5,sK3)
% 7.58/1.51      | ~ v1_relat_1(sK5)
% 7.58/1.51      | k7_relat_1(sK5,sK3) = sK5 ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_399]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3543,plain,
% 7.58/1.51      ( k7_relat_1(sK5,sK3) = sK5 ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_3413,c_22,c_1628,c_1827,c_2226]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_8883,plain,
% 7.58/1.51      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.58/1.51      inference(light_normalisation,[status(thm)],[c_8877,c_3543]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_0,plain,
% 7.58/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.58/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_409,plain,
% 7.58/1.51      ( k3_xboole_0(X0_51,X1_51) = k3_xboole_0(X1_51,X0_51) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_8,plain,
% 7.58/1.51      ( ~ v1_relat_1(X0)
% 7.58/1.51      | k3_xboole_0(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.58/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_401,plain,
% 7.58/1.51      ( ~ v1_relat_1(X0_51)
% 7.58/1.51      | k3_xboole_0(k7_relat_1(X0_51,X1_51),k7_relat_1(X0_51,X2_51)) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51)) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1188,plain,
% 7.58/1.51      ( k3_xboole_0(k7_relat_1(X0_51,X1_51),k7_relat_1(X0_51,X2_51)) = k7_relat_1(X0_51,k3_xboole_0(X1_51,X2_51))
% 7.58/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3400,plain,
% 7.58/1.51      ( k3_xboole_0(k7_relat_1(sK5,X0_51),k7_relat_1(sK5,X1_51)) = k7_relat_1(sK5,k3_xboole_0(X0_51,X1_51)) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_2743,c_1188]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3644,plain,
% 7.58/1.51      ( k7_relat_1(sK5,k3_xboole_0(sK3,X0_51)) = k3_xboole_0(sK5,k7_relat_1(sK5,X0_51)) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_3543,c_3400]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3756,plain,
% 7.58/1.51      ( k7_relat_1(sK5,k3_xboole_0(X0_51,sK3)) = k3_xboole_0(sK5,k7_relat_1(sK5,X0_51)) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_409,c_3644]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_4772,plain,
% 7.58/1.51      ( k3_xboole_0(sK5,k7_relat_1(sK5,sK2)) = k7_relat_1(sK5,k1_xboole_0) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_4650,c_3756]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_9164,plain,
% 7.58/1.51      ( k7_relat_1(sK5,k1_xboole_0) = k3_xboole_0(sK5,k1_xboole_0) ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_8883,c_4772]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_4,plain,
% 7.58/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_405,plain,
% 7.58/1.51      ( k3_xboole_0(X0_51,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_9166,plain,
% 7.58/1.51      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_9164,c_405]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14359,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(light_normalisation,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_14358,c_4650,c_9166]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3175,plain,
% 7.58/1.51      ( v4_relat_1(sK4,sK2) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_1202,c_1193]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3540,plain,
% 7.58/1.51      ( k7_relat_1(sK4,sK2) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_3175,c_1190]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1631,plain,
% 7.58/1.51      ( v4_relat_1(sK4,sK2)
% 7.58/1.51      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_396]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1830,plain,
% 7.58/1.51      ( ~ v4_relat_1(sK4,sK2)
% 7.58/1.51      | ~ v1_relat_1(sK4)
% 7.58/1.51      | k7_relat_1(sK4,sK2) = sK4 ),
% 7.58/1.51      inference(instantiation,[status(thm)],[c_399]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2166,plain,
% 7.58/1.51      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4) ),
% 7.58/1.51      inference(resolution,[status(thm)],[c_403,c_386]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2233,plain,
% 7.58/1.51      ( v1_relat_1(sK4) ),
% 7.58/1.51      inference(forward_subsumption_resolution,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_2166,c_402]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3638,plain,
% 7.58/1.51      ( k7_relat_1(sK4,sK2) = sK4 ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_3540,c_25,c_1631,c_1830,c_2233]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2294,plain,
% 7.58/1.51      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.58/1.51      | v1_relat_1(sK4) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_1202,c_1186]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2234,plain,
% 7.58/1.51      ( v1_relat_1(sK4) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2868,plain,
% 7.58/1.51      ( v1_relat_1(sK4) = iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_2294,c_2234]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3401,plain,
% 7.58/1.51      ( k3_xboole_0(k7_relat_1(sK4,X0_51),k7_relat_1(sK4,X1_51)) = k7_relat_1(sK4,k3_xboole_0(X0_51,X1_51)) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_2868,c_1188]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_3728,plain,
% 7.58/1.51      ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_51)) = k3_xboole_0(sK4,k7_relat_1(sK4,X0_51)) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_3638,c_3401]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14360,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k3_xboole_0(sK4,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_14359,c_2066,c_3728]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5617,plain,
% 7.58/1.51      ( k7_relat_1(k7_relat_1(X0_51,sK2),sK3) = k1_xboole_0
% 7.58/1.51      | v1_relat_1(X0_51) != iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_4643,c_1189]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5930,plain,
% 7.58/1.51      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_2868,c_5617]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5932,plain,
% 7.58/1.51      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.58/1.51      inference(light_normalisation,[status(thm)],[c_5930,c_3638]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14361,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k3_xboole_0(sK4,k1_xboole_0) != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(light_normalisation,[status(thm)],[c_14360,c_5932]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14362,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | k1_xboole_0 != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_14361,c_405]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_14363,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(equality_resolution_simp,[status(thm)],[c_14362]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_17,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1)
% 7.58/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.58/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_341,plain,
% 7.58/1.51      ( ~ v1_funct_1(X3)
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X1)
% 7.58/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_17,c_20,c_19,c_18]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_342,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.51      | ~ v1_funct_2(X3,X4,X2)
% 7.58/1.51      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.58/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.58/1.51      | ~ v1_funct_1(X0)
% 7.58/1.51      | ~ v1_funct_1(X3)
% 7.58/1.51      | v1_xboole_0(X1)
% 7.58/1.51      | v1_xboole_0(X2)
% 7.58/1.51      | v1_xboole_0(X4)
% 7.58/1.51      | v1_xboole_0(X5)
% 7.58/1.51      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.58/1.51      inference(renaming,[status(thm)],[c_341]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_376,plain,
% 7.58/1.51      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.58/1.51      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.58/1.51      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.58/1.51      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.58/1.51      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.58/1.51      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.58/1.51      | ~ v1_funct_1(X0_51)
% 7.58/1.51      | ~ v1_funct_1(X3_51)
% 7.58/1.51      | v1_xboole_0(X1_51)
% 7.58/1.51      | v1_xboole_0(X2_51)
% 7.58/1.51      | v1_xboole_0(X4_51)
% 7.58/1.51      | v1_xboole_0(X5_51)
% 7.58/1.51      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_342]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_1212,plain,
% 7.58/1.51      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
% 7.58/1.51      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 7.58/1.51      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 7.58/1.51      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.58/1.51      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 7.58/1.51      | v1_funct_1(X2_51) != iProver_top
% 7.58/1.51      | v1_funct_1(X5_51) != iProver_top
% 7.58/1.51      | v1_xboole_0(X3_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X1_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X4_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_9884,plain,
% 7.58/1.51      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.58/1.51      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.58/1.51      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | v1_funct_1(X1_51) != iProver_top
% 7.58/1.51      | v1_funct_1(sK5) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X2_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK1) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK3) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_5861,c_1212]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10578,plain,
% 7.58/1.51      ( v1_funct_1(X1_51) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.58/1.51      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.58/1.51      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X2_51) = iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_9884,c_36,c_39,c_45,c_46,c_47]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10579,plain,
% 7.58/1.51      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.58/1.51      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.58/1.51      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.58/1.51      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.58/1.51      | v1_funct_1(X1_51) != iProver_top
% 7.58/1.51      | v1_xboole_0(X2_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(renaming,[status(thm)],[c_10578]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10594,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.58/1.51      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.58/1.51      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | v1_funct_1(sK4) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | v1_xboole_0(sK2) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_5921,c_10579]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10757,plain,
% 7.58/1.51      ( v1_xboole_0(X0_51) = iProver_top
% 7.58/1.51      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.58/1.51      inference(global_propositional_subsumption,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_10594,c_37,c_42,c_43,c_44]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10758,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.58/1.51      | v1_xboole_0(X0_51) = iProver_top ),
% 7.58/1.51      inference(renaming,[status(thm)],[c_10757]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10768,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_2066,c_10758]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10769,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(light_normalisation,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_10768,c_4650,c_9166]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10770,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k3_xboole_0(sK4,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_10769,c_2066,c_3728]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10771,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k3_xboole_0(sK4,k1_xboole_0) != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(light_normalisation,[status(thm)],[c_10770,c_5932]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10772,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | k1_xboole_0 != k1_xboole_0
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_10771,c_405]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_10773,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.58/1.51      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.58/1.51      | v1_xboole_0(sK0) = iProver_top ),
% 7.58/1.51      inference(equality_resolution_simp,[status(thm)],[c_10772]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5327,plain,
% 7.58/1.51      ( k3_xboole_0(sK4,k7_relat_1(sK4,sK3)) = k7_relat_1(sK4,k1_xboole_0) ),
% 7.58/1.51      inference(superposition,[status(thm)],[c_4650,c_3728]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_6200,plain,
% 7.58/1.51      ( k7_relat_1(sK4,k1_xboole_0) = k3_xboole_0(sK4,k1_xboole_0) ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_5932,c_5327]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_6201,plain,
% 7.58/1.51      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_6200,c_405]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_21,negated_conjecture,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.58/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_390,negated_conjecture,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.58/1.51      inference(subtyping,[status(esa)],[c_21]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_2216,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_2066,c_390]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_4769,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_4650,c_2216]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_5865,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_5861,c_4769]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_6045,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_5865,c_5921]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_6612,plain,
% 7.58/1.51      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.58/1.51      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.58/1.51      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0 ),
% 7.58/1.51      inference(demodulation,[status(thm)],[c_6201,c_6045]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_40,plain,
% 7.58/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_31,negated_conjecture,
% 7.58/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.58/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_38,plain,
% 7.58/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_34,negated_conjecture,
% 7.58/1.51      ( ~ v1_xboole_0(sK0) ),
% 7.58/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(c_35,plain,
% 7.58/1.51      ( v1_xboole_0(sK0) != iProver_top ),
% 7.58/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.58/1.51  
% 7.58/1.51  cnf(contradiction,plain,
% 7.58/1.51      ( $false ),
% 7.58/1.51      inference(minisat,
% 7.58/1.51                [status(thm)],
% 7.58/1.51                [c_14363,c_10773,c_9166,c_6612,c_40,c_38,c_35]) ).
% 7.58/1.51  
% 7.58/1.51  
% 7.58/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.51  
% 7.58/1.51  ------                               Statistics
% 7.58/1.51  
% 7.58/1.51  ------ Selected
% 7.58/1.51  
% 7.58/1.51  total_time:                             0.624
% 7.58/1.51  
%------------------------------------------------------------------------------
