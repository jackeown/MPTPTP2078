%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:40 EST 2020

% Result     : Theorem 7.09s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  218 (2282 expanded)
%              Number of clauses        :  150 ( 626 expanded)
%              Number of leaves         :   18 ( 877 expanded)
%              Depth                    :   26
%              Number of atoms          : 1280 (29189 expanded)
%              Number of equality atoms :  566 (7057 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

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
    inference(ennf_transformation,[],[f16])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f48,f47,f46,f45,f44,f43])).

fof(f85,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    v1_funct_1(sK4) ),
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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f32])).

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

fof(f68,plain,(
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

fof(f90,plain,(
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
    inference(equality_resolution,[],[f68])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f70,plain,(
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

fof(f71,plain,(
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

fof(f72,plain,(
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

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f67,plain,(
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

fof(f91,plain,(
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
    inference(equality_resolution,[],[f67])).

fof(f86,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_854,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1387,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_860,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1382,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_860])).

cnf(c_2722,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1382])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1822,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1988,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_1822])).

cnf(c_3005,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2722,c_26,c_24,c_1988])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_848,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1393,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_864,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1378,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_864])).

cnf(c_2233,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1393,c_1378])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_851,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1390,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_2723,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1382])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1827,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_860])).

cnf(c_1993,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1827])).

cnf(c_3121,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2723,c_29,c_27,c_1993])).

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
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f72])).

cnf(c_207,plain,
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

cnf(c_208,plain,
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
    inference(renaming,[status(thm)],[c_207])).

cnf(c_841,plain,
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
    inference(subtyping,[status(esa)],[c_208])).

cnf(c_1400,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_863,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1379,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_863])).

cnf(c_1618,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
    | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1400,c_1379])).

cnf(c_5830,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_1618])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_17626,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5830,c_38,c_39,c_44,c_45,c_46])).

cnf(c_17627,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_17626])).

cnf(c_17648,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_17627])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_269,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_510,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_30])).

cnf(c_511,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_513,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_34,c_32])).

cnf(c_599,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_269,c_513])).

cnf(c_600,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_836,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_17745,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17648,c_836])).

cnf(c_17746,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17745,c_2233])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_862,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1380,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_862])).

cnf(c_2695,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1380])).

cnf(c_1746,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1930,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1931,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_861,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1974,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1975,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1974])).

cnf(c_2998,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2695,c_46,c_1931,c_1975])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_604,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_605,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_835,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_1404,plain,
    ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_3003,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2998,c_1404])).

cnf(c_17747,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17746,c_836,c_3003])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18112,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17747,c_40,c_41,c_42])).

cnf(c_18113,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_18112])).

cnf(c_18123,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_18113])).

cnf(c_2694,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1380])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1927,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1746])).

cnf(c_1928,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1927])).

cnf(c_1971,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1972,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_2933,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2694,c_49,c_1928,c_1972])).

cnf(c_2938,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2933,c_1404])).

cnf(c_18124,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18123,c_2938])).

cnf(c_18125,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18124])).

cnf(c_858,plain,
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

cnf(c_1384,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_1563,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1384,c_1379])).

cnf(c_3634,plain,
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
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1382])).

cnf(c_856,plain,
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

cnf(c_1386,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_1511,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1386,c_1379])).

cnf(c_9292,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3634,c_1511])).

cnf(c_9296,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_9292])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9449,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9296,c_38,c_41,c_47,c_48])).

cnf(c_9450,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_9449])).

cnf(c_9463,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_9450])).

cnf(c_9745,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9463,c_39,c_44,c_45])).

cnf(c_9754,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_9745])).

cnf(c_9824,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9754,c_40])).

cnf(c_18126,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18125,c_9824])).

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
    inference(cnf_transformation,[],[f91])).

cnf(c_200,plain,
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

cnf(c_201,plain,
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
    inference(renaming,[status(thm)],[c_200])).

cnf(c_842,plain,
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
    inference(subtyping,[status(esa)],[c_201])).

cnf(c_1399,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_1590,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
    | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
    | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X4_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1399,c_1379])).

cnf(c_5009,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3121,c_1590])).

cnf(c_13991,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5009,c_38,c_39,c_44,c_45,c_46])).

cnf(c_13992,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_13991])).

cnf(c_14013,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_13992])).

cnf(c_14110,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14013,c_836])).

cnf(c_14111,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14110,c_2233])).

cnf(c_14112,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14111,c_836,c_3003])).

cnf(c_14436,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14112,c_40,c_41,c_42])).

cnf(c_14437,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_53,sK3,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_14436])).

cnf(c_14447,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3005,c_14437])).

cnf(c_14448,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14447,c_2938])).

cnf(c_14449,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14448])).

cnf(c_14450,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14449,c_9824])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_855,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2620,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2233,c_855])).

cnf(c_2621,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2620,c_836])).

cnf(c_3269,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2621,c_3005,c_3121])).

cnf(c_3274,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2938,c_3269])).

cnf(c_2812,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_3411,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3274,c_27,c_1930,c_1974,c_2812])).

cnf(c_3412,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_3411])).

cnf(c_9828,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_9824,c_3412])).

cnf(c_9829,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_9828,c_9824])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18126,c_14450,c_9829,c_49,c_48,c_47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.09/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/1.49  
% 7.09/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.09/1.49  
% 7.09/1.49  ------  iProver source info
% 7.09/1.49  
% 7.09/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.09/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.09/1.49  git: non_committed_changes: false
% 7.09/1.49  git: last_make_outside_of_git: false
% 7.09/1.49  
% 7.09/1.49  ------ 
% 7.09/1.49  
% 7.09/1.49  ------ Input Options
% 7.09/1.49  
% 7.09/1.49  --out_options                           all
% 7.09/1.49  --tptp_safe_out                         true
% 7.09/1.49  --problem_path                          ""
% 7.09/1.49  --include_path                          ""
% 7.09/1.49  --clausifier                            res/vclausify_rel
% 7.09/1.49  --clausifier_options                    --mode clausify
% 7.09/1.49  --stdin                                 false
% 7.09/1.49  --stats_out                             all
% 7.09/1.49  
% 7.09/1.49  ------ General Options
% 7.09/1.49  
% 7.09/1.49  --fof                                   false
% 7.09/1.49  --time_out_real                         305.
% 7.09/1.49  --time_out_virtual                      -1.
% 7.09/1.49  --symbol_type_check                     false
% 7.09/1.49  --clausify_out                          false
% 7.09/1.49  --sig_cnt_out                           false
% 7.09/1.49  --trig_cnt_out                          false
% 7.09/1.49  --trig_cnt_out_tolerance                1.
% 7.09/1.49  --trig_cnt_out_sk_spl                   false
% 7.09/1.49  --abstr_cl_out                          false
% 7.09/1.49  
% 7.09/1.49  ------ Global Options
% 7.09/1.49  
% 7.09/1.49  --schedule                              default
% 7.09/1.49  --add_important_lit                     false
% 7.09/1.49  --prop_solver_per_cl                    1000
% 7.09/1.49  --min_unsat_core                        false
% 7.09/1.49  --soft_assumptions                      false
% 7.09/1.49  --soft_lemma_size                       3
% 7.09/1.49  --prop_impl_unit_size                   0
% 7.09/1.49  --prop_impl_unit                        []
% 7.09/1.49  --share_sel_clauses                     true
% 7.09/1.49  --reset_solvers                         false
% 7.09/1.49  --bc_imp_inh                            [conj_cone]
% 7.09/1.49  --conj_cone_tolerance                   3.
% 7.09/1.49  --extra_neg_conj                        none
% 7.09/1.49  --large_theory_mode                     true
% 7.09/1.49  --prolific_symb_bound                   200
% 7.09/1.49  --lt_threshold                          2000
% 7.09/1.49  --clause_weak_htbl                      true
% 7.09/1.49  --gc_record_bc_elim                     false
% 7.09/1.49  
% 7.09/1.49  ------ Preprocessing Options
% 7.09/1.49  
% 7.09/1.49  --preprocessing_flag                    true
% 7.09/1.49  --time_out_prep_mult                    0.1
% 7.09/1.49  --splitting_mode                        input
% 7.09/1.49  --splitting_grd                         true
% 7.09/1.49  --splitting_cvd                         false
% 7.09/1.49  --splitting_cvd_svl                     false
% 7.09/1.49  --splitting_nvd                         32
% 7.09/1.49  --sub_typing                            true
% 7.09/1.49  --prep_gs_sim                           true
% 7.09/1.49  --prep_unflatten                        true
% 7.09/1.49  --prep_res_sim                          true
% 7.09/1.49  --prep_upred                            true
% 7.09/1.49  --prep_sem_filter                       exhaustive
% 7.09/1.49  --prep_sem_filter_out                   false
% 7.09/1.49  --pred_elim                             true
% 7.09/1.49  --res_sim_input                         true
% 7.09/1.49  --eq_ax_congr_red                       true
% 7.09/1.49  --pure_diseq_elim                       true
% 7.09/1.49  --brand_transform                       false
% 7.09/1.49  --non_eq_to_eq                          false
% 7.09/1.49  --prep_def_merge                        true
% 7.09/1.49  --prep_def_merge_prop_impl              false
% 7.09/1.49  --prep_def_merge_mbd                    true
% 7.09/1.49  --prep_def_merge_tr_red                 false
% 7.09/1.49  --prep_def_merge_tr_cl                  false
% 7.09/1.49  --smt_preprocessing                     true
% 7.09/1.49  --smt_ac_axioms                         fast
% 7.09/1.49  --preprocessed_out                      false
% 7.09/1.49  --preprocessed_stats                    false
% 7.09/1.49  
% 7.09/1.49  ------ Abstraction refinement Options
% 7.09/1.49  
% 7.09/1.49  --abstr_ref                             []
% 7.09/1.49  --abstr_ref_prep                        false
% 7.09/1.49  --abstr_ref_until_sat                   false
% 7.09/1.49  --abstr_ref_sig_restrict                funpre
% 7.09/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.09/1.49  --abstr_ref_under                       []
% 7.09/1.49  
% 7.09/1.49  ------ SAT Options
% 7.09/1.49  
% 7.09/1.49  --sat_mode                              false
% 7.09/1.49  --sat_fm_restart_options                ""
% 7.09/1.49  --sat_gr_def                            false
% 7.09/1.49  --sat_epr_types                         true
% 7.09/1.49  --sat_non_cyclic_types                  false
% 7.09/1.49  --sat_finite_models                     false
% 7.09/1.49  --sat_fm_lemmas                         false
% 7.09/1.49  --sat_fm_prep                           false
% 7.09/1.49  --sat_fm_uc_incr                        true
% 7.09/1.49  --sat_out_model                         small
% 7.09/1.49  --sat_out_clauses                       false
% 7.09/1.49  
% 7.09/1.49  ------ QBF Options
% 7.09/1.49  
% 7.09/1.49  --qbf_mode                              false
% 7.09/1.49  --qbf_elim_univ                         false
% 7.09/1.49  --qbf_dom_inst                          none
% 7.09/1.49  --qbf_dom_pre_inst                      false
% 7.09/1.49  --qbf_sk_in                             false
% 7.09/1.49  --qbf_pred_elim                         true
% 7.09/1.49  --qbf_split                             512
% 7.09/1.49  
% 7.09/1.49  ------ BMC1 Options
% 7.09/1.49  
% 7.09/1.49  --bmc1_incremental                      false
% 7.09/1.49  --bmc1_axioms                           reachable_all
% 7.09/1.49  --bmc1_min_bound                        0
% 7.09/1.49  --bmc1_max_bound                        -1
% 7.09/1.49  --bmc1_max_bound_default                -1
% 7.09/1.49  --bmc1_symbol_reachability              true
% 7.09/1.49  --bmc1_property_lemmas                  false
% 7.09/1.49  --bmc1_k_induction                      false
% 7.09/1.49  --bmc1_non_equiv_states                 false
% 7.09/1.49  --bmc1_deadlock                         false
% 7.09/1.49  --bmc1_ucm                              false
% 7.09/1.49  --bmc1_add_unsat_core                   none
% 7.09/1.49  --bmc1_unsat_core_children              false
% 7.09/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.09/1.49  --bmc1_out_stat                         full
% 7.09/1.49  --bmc1_ground_init                      false
% 7.09/1.49  --bmc1_pre_inst_next_state              false
% 7.09/1.49  --bmc1_pre_inst_state                   false
% 7.09/1.49  --bmc1_pre_inst_reach_state             false
% 7.09/1.49  --bmc1_out_unsat_core                   false
% 7.09/1.49  --bmc1_aig_witness_out                  false
% 7.09/1.49  --bmc1_verbose                          false
% 7.09/1.49  --bmc1_dump_clauses_tptp                false
% 7.09/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.09/1.49  --bmc1_dump_file                        -
% 7.09/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.09/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.09/1.49  --bmc1_ucm_extend_mode                  1
% 7.09/1.49  --bmc1_ucm_init_mode                    2
% 7.09/1.49  --bmc1_ucm_cone_mode                    none
% 7.09/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.09/1.49  --bmc1_ucm_relax_model                  4
% 7.09/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.09/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.09/1.49  --bmc1_ucm_layered_model                none
% 7.09/1.49  --bmc1_ucm_max_lemma_size               10
% 7.09/1.49  
% 7.09/1.49  ------ AIG Options
% 7.09/1.49  
% 7.09/1.49  --aig_mode                              false
% 7.09/1.49  
% 7.09/1.49  ------ Instantiation Options
% 7.09/1.49  
% 7.09/1.49  --instantiation_flag                    true
% 7.09/1.49  --inst_sos_flag                         false
% 7.09/1.49  --inst_sos_phase                        true
% 7.09/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.09/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.09/1.49  --inst_lit_sel_side                     num_symb
% 7.09/1.49  --inst_solver_per_active                1400
% 7.09/1.49  --inst_solver_calls_frac                1.
% 7.09/1.49  --inst_passive_queue_type               priority_queues
% 7.09/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.09/1.49  --inst_passive_queues_freq              [25;2]
% 7.09/1.49  --inst_dismatching                      true
% 7.09/1.49  --inst_eager_unprocessed_to_passive     true
% 7.09/1.49  --inst_prop_sim_given                   true
% 7.09/1.49  --inst_prop_sim_new                     false
% 7.09/1.49  --inst_subs_new                         false
% 7.09/1.49  --inst_eq_res_simp                      false
% 7.09/1.49  --inst_subs_given                       false
% 7.09/1.49  --inst_orphan_elimination               true
% 7.09/1.49  --inst_learning_loop_flag               true
% 7.09/1.49  --inst_learning_start                   3000
% 7.09/1.49  --inst_learning_factor                  2
% 7.09/1.49  --inst_start_prop_sim_after_learn       3
% 7.09/1.49  --inst_sel_renew                        solver
% 7.09/1.49  --inst_lit_activity_flag                true
% 7.09/1.49  --inst_restr_to_given                   false
% 7.09/1.49  --inst_activity_threshold               500
% 7.09/1.49  --inst_out_proof                        true
% 7.09/1.49  
% 7.09/1.49  ------ Resolution Options
% 7.09/1.49  
% 7.09/1.49  --resolution_flag                       true
% 7.09/1.49  --res_lit_sel                           adaptive
% 7.09/1.49  --res_lit_sel_side                      none
% 7.09/1.49  --res_ordering                          kbo
% 7.09/1.49  --res_to_prop_solver                    active
% 7.09/1.49  --res_prop_simpl_new                    false
% 7.09/1.49  --res_prop_simpl_given                  true
% 7.09/1.49  --res_passive_queue_type                priority_queues
% 7.09/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.09/1.49  --res_passive_queues_freq               [15;5]
% 7.09/1.49  --res_forward_subs                      full
% 7.09/1.49  --res_backward_subs                     full
% 7.09/1.49  --res_forward_subs_resolution           true
% 7.09/1.49  --res_backward_subs_resolution          true
% 7.09/1.49  --res_orphan_elimination                true
% 7.09/1.49  --res_time_limit                        2.
% 7.09/1.49  --res_out_proof                         true
% 7.09/1.49  
% 7.09/1.49  ------ Superposition Options
% 7.09/1.49  
% 7.09/1.49  --superposition_flag                    true
% 7.09/1.49  --sup_passive_queue_type                priority_queues
% 7.09/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.09/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.09/1.49  --demod_completeness_check              fast
% 7.09/1.49  --demod_use_ground                      true
% 7.09/1.49  --sup_to_prop_solver                    passive
% 7.09/1.49  --sup_prop_simpl_new                    true
% 7.09/1.49  --sup_prop_simpl_given                  true
% 7.09/1.49  --sup_fun_splitting                     false
% 7.09/1.49  --sup_smt_interval                      50000
% 7.09/1.49  
% 7.09/1.49  ------ Superposition Simplification Setup
% 7.09/1.49  
% 7.09/1.49  --sup_indices_passive                   []
% 7.09/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.09/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.09/1.49  --sup_full_bw                           [BwDemod]
% 7.09/1.49  --sup_immed_triv                        [TrivRules]
% 7.09/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.09/1.49  --sup_immed_bw_main                     []
% 7.09/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.09/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.09/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.09/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.09/1.49  
% 7.09/1.49  ------ Combination Options
% 7.09/1.49  
% 7.09/1.49  --comb_res_mult                         3
% 7.09/1.49  --comb_sup_mult                         2
% 7.09/1.49  --comb_inst_mult                        10
% 7.09/1.49  
% 7.09/1.49  ------ Debug Options
% 7.09/1.49  
% 7.09/1.49  --dbg_backtrace                         false
% 7.09/1.49  --dbg_dump_prop_clauses                 false
% 7.09/1.49  --dbg_dump_prop_clauses_file            -
% 7.09/1.49  --dbg_out_stat                          false
% 7.09/1.49  ------ Parsing...
% 7.09/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.09/1.49  
% 7.09/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.09/1.49  
% 7.09/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.09/1.49  
% 7.09/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.09/1.49  ------ Proving...
% 7.09/1.49  ------ Problem Properties 
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  clauses                                 31
% 7.09/1.49  conjectures                             13
% 7.09/1.49  EPR                                     8
% 7.09/1.49  Horn                                    24
% 7.09/1.49  unary                                   15
% 7.09/1.49  binary                                  2
% 7.09/1.49  lits                                    130
% 7.09/1.49  lits eq                                 21
% 7.09/1.49  fd_pure                                 0
% 7.09/1.49  fd_pseudo                               0
% 7.09/1.49  fd_cond                                 0
% 7.09/1.49  fd_pseudo_cond                          1
% 7.09/1.49  AC symbols                              0
% 7.09/1.49  
% 7.09/1.49  ------ Schedule dynamic 5 is on 
% 7.09/1.49  
% 7.09/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  ------ 
% 7.09/1.49  Current options:
% 7.09/1.49  ------ 
% 7.09/1.49  
% 7.09/1.49  ------ Input Options
% 7.09/1.49  
% 7.09/1.49  --out_options                           all
% 7.09/1.49  --tptp_safe_out                         true
% 7.09/1.49  --problem_path                          ""
% 7.09/1.49  --include_path                          ""
% 7.09/1.49  --clausifier                            res/vclausify_rel
% 7.09/1.49  --clausifier_options                    --mode clausify
% 7.09/1.49  --stdin                                 false
% 7.09/1.49  --stats_out                             all
% 7.09/1.49  
% 7.09/1.49  ------ General Options
% 7.09/1.49  
% 7.09/1.49  --fof                                   false
% 7.09/1.49  --time_out_real                         305.
% 7.09/1.49  --time_out_virtual                      -1.
% 7.09/1.49  --symbol_type_check                     false
% 7.09/1.49  --clausify_out                          false
% 7.09/1.49  --sig_cnt_out                           false
% 7.09/1.49  --trig_cnt_out                          false
% 7.09/1.49  --trig_cnt_out_tolerance                1.
% 7.09/1.49  --trig_cnt_out_sk_spl                   false
% 7.09/1.49  --abstr_cl_out                          false
% 7.09/1.49  
% 7.09/1.49  ------ Global Options
% 7.09/1.49  
% 7.09/1.49  --schedule                              default
% 7.09/1.49  --add_important_lit                     false
% 7.09/1.49  --prop_solver_per_cl                    1000
% 7.09/1.49  --min_unsat_core                        false
% 7.09/1.49  --soft_assumptions                      false
% 7.09/1.49  --soft_lemma_size                       3
% 7.09/1.49  --prop_impl_unit_size                   0
% 7.09/1.49  --prop_impl_unit                        []
% 7.09/1.49  --share_sel_clauses                     true
% 7.09/1.49  --reset_solvers                         false
% 7.09/1.49  --bc_imp_inh                            [conj_cone]
% 7.09/1.49  --conj_cone_tolerance                   3.
% 7.09/1.49  --extra_neg_conj                        none
% 7.09/1.49  --large_theory_mode                     true
% 7.09/1.49  --prolific_symb_bound                   200
% 7.09/1.49  --lt_threshold                          2000
% 7.09/1.49  --clause_weak_htbl                      true
% 7.09/1.49  --gc_record_bc_elim                     false
% 7.09/1.49  
% 7.09/1.49  ------ Preprocessing Options
% 7.09/1.49  
% 7.09/1.49  --preprocessing_flag                    true
% 7.09/1.49  --time_out_prep_mult                    0.1
% 7.09/1.49  --splitting_mode                        input
% 7.09/1.49  --splitting_grd                         true
% 7.09/1.49  --splitting_cvd                         false
% 7.09/1.49  --splitting_cvd_svl                     false
% 7.09/1.49  --splitting_nvd                         32
% 7.09/1.49  --sub_typing                            true
% 7.09/1.49  --prep_gs_sim                           true
% 7.09/1.49  --prep_unflatten                        true
% 7.09/1.49  --prep_res_sim                          true
% 7.09/1.49  --prep_upred                            true
% 7.09/1.49  --prep_sem_filter                       exhaustive
% 7.09/1.49  --prep_sem_filter_out                   false
% 7.09/1.49  --pred_elim                             true
% 7.09/1.49  --res_sim_input                         true
% 7.09/1.49  --eq_ax_congr_red                       true
% 7.09/1.49  --pure_diseq_elim                       true
% 7.09/1.49  --brand_transform                       false
% 7.09/1.49  --non_eq_to_eq                          false
% 7.09/1.49  --prep_def_merge                        true
% 7.09/1.49  --prep_def_merge_prop_impl              false
% 7.09/1.49  --prep_def_merge_mbd                    true
% 7.09/1.49  --prep_def_merge_tr_red                 false
% 7.09/1.49  --prep_def_merge_tr_cl                  false
% 7.09/1.49  --smt_preprocessing                     true
% 7.09/1.49  --smt_ac_axioms                         fast
% 7.09/1.49  --preprocessed_out                      false
% 7.09/1.49  --preprocessed_stats                    false
% 7.09/1.49  
% 7.09/1.49  ------ Abstraction refinement Options
% 7.09/1.49  
% 7.09/1.49  --abstr_ref                             []
% 7.09/1.49  --abstr_ref_prep                        false
% 7.09/1.49  --abstr_ref_until_sat                   false
% 7.09/1.49  --abstr_ref_sig_restrict                funpre
% 7.09/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.09/1.49  --abstr_ref_under                       []
% 7.09/1.49  
% 7.09/1.49  ------ SAT Options
% 7.09/1.49  
% 7.09/1.49  --sat_mode                              false
% 7.09/1.49  --sat_fm_restart_options                ""
% 7.09/1.49  --sat_gr_def                            false
% 7.09/1.49  --sat_epr_types                         true
% 7.09/1.49  --sat_non_cyclic_types                  false
% 7.09/1.49  --sat_finite_models                     false
% 7.09/1.49  --sat_fm_lemmas                         false
% 7.09/1.49  --sat_fm_prep                           false
% 7.09/1.49  --sat_fm_uc_incr                        true
% 7.09/1.49  --sat_out_model                         small
% 7.09/1.49  --sat_out_clauses                       false
% 7.09/1.49  
% 7.09/1.49  ------ QBF Options
% 7.09/1.49  
% 7.09/1.49  --qbf_mode                              false
% 7.09/1.49  --qbf_elim_univ                         false
% 7.09/1.49  --qbf_dom_inst                          none
% 7.09/1.49  --qbf_dom_pre_inst                      false
% 7.09/1.49  --qbf_sk_in                             false
% 7.09/1.49  --qbf_pred_elim                         true
% 7.09/1.49  --qbf_split                             512
% 7.09/1.49  
% 7.09/1.49  ------ BMC1 Options
% 7.09/1.49  
% 7.09/1.49  --bmc1_incremental                      false
% 7.09/1.49  --bmc1_axioms                           reachable_all
% 7.09/1.49  --bmc1_min_bound                        0
% 7.09/1.49  --bmc1_max_bound                        -1
% 7.09/1.49  --bmc1_max_bound_default                -1
% 7.09/1.49  --bmc1_symbol_reachability              true
% 7.09/1.49  --bmc1_property_lemmas                  false
% 7.09/1.49  --bmc1_k_induction                      false
% 7.09/1.49  --bmc1_non_equiv_states                 false
% 7.09/1.49  --bmc1_deadlock                         false
% 7.09/1.49  --bmc1_ucm                              false
% 7.09/1.49  --bmc1_add_unsat_core                   none
% 7.09/1.49  --bmc1_unsat_core_children              false
% 7.09/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.09/1.49  --bmc1_out_stat                         full
% 7.09/1.49  --bmc1_ground_init                      false
% 7.09/1.49  --bmc1_pre_inst_next_state              false
% 7.09/1.49  --bmc1_pre_inst_state                   false
% 7.09/1.49  --bmc1_pre_inst_reach_state             false
% 7.09/1.49  --bmc1_out_unsat_core                   false
% 7.09/1.49  --bmc1_aig_witness_out                  false
% 7.09/1.49  --bmc1_verbose                          false
% 7.09/1.49  --bmc1_dump_clauses_tptp                false
% 7.09/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.09/1.49  --bmc1_dump_file                        -
% 7.09/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.09/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.09/1.49  --bmc1_ucm_extend_mode                  1
% 7.09/1.49  --bmc1_ucm_init_mode                    2
% 7.09/1.49  --bmc1_ucm_cone_mode                    none
% 7.09/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.09/1.49  --bmc1_ucm_relax_model                  4
% 7.09/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.09/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.09/1.49  --bmc1_ucm_layered_model                none
% 7.09/1.49  --bmc1_ucm_max_lemma_size               10
% 7.09/1.49  
% 7.09/1.49  ------ AIG Options
% 7.09/1.49  
% 7.09/1.49  --aig_mode                              false
% 7.09/1.49  
% 7.09/1.49  ------ Instantiation Options
% 7.09/1.49  
% 7.09/1.49  --instantiation_flag                    true
% 7.09/1.49  --inst_sos_flag                         false
% 7.09/1.49  --inst_sos_phase                        true
% 7.09/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.09/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.09/1.49  --inst_lit_sel_side                     none
% 7.09/1.49  --inst_solver_per_active                1400
% 7.09/1.49  --inst_solver_calls_frac                1.
% 7.09/1.49  --inst_passive_queue_type               priority_queues
% 7.09/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.09/1.49  --inst_passive_queues_freq              [25;2]
% 7.09/1.49  --inst_dismatching                      true
% 7.09/1.49  --inst_eager_unprocessed_to_passive     true
% 7.09/1.49  --inst_prop_sim_given                   true
% 7.09/1.49  --inst_prop_sim_new                     false
% 7.09/1.49  --inst_subs_new                         false
% 7.09/1.49  --inst_eq_res_simp                      false
% 7.09/1.49  --inst_subs_given                       false
% 7.09/1.49  --inst_orphan_elimination               true
% 7.09/1.49  --inst_learning_loop_flag               true
% 7.09/1.49  --inst_learning_start                   3000
% 7.09/1.49  --inst_learning_factor                  2
% 7.09/1.49  --inst_start_prop_sim_after_learn       3
% 7.09/1.49  --inst_sel_renew                        solver
% 7.09/1.49  --inst_lit_activity_flag                true
% 7.09/1.49  --inst_restr_to_given                   false
% 7.09/1.49  --inst_activity_threshold               500
% 7.09/1.49  --inst_out_proof                        true
% 7.09/1.49  
% 7.09/1.49  ------ Resolution Options
% 7.09/1.49  
% 7.09/1.49  --resolution_flag                       false
% 7.09/1.49  --res_lit_sel                           adaptive
% 7.09/1.49  --res_lit_sel_side                      none
% 7.09/1.49  --res_ordering                          kbo
% 7.09/1.49  --res_to_prop_solver                    active
% 7.09/1.49  --res_prop_simpl_new                    false
% 7.09/1.49  --res_prop_simpl_given                  true
% 7.09/1.49  --res_passive_queue_type                priority_queues
% 7.09/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.09/1.49  --res_passive_queues_freq               [15;5]
% 7.09/1.49  --res_forward_subs                      full
% 7.09/1.49  --res_backward_subs                     full
% 7.09/1.49  --res_forward_subs_resolution           true
% 7.09/1.49  --res_backward_subs_resolution          true
% 7.09/1.49  --res_orphan_elimination                true
% 7.09/1.49  --res_time_limit                        2.
% 7.09/1.49  --res_out_proof                         true
% 7.09/1.49  
% 7.09/1.49  ------ Superposition Options
% 7.09/1.49  
% 7.09/1.49  --superposition_flag                    true
% 7.09/1.49  --sup_passive_queue_type                priority_queues
% 7.09/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.09/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.09/1.49  --demod_completeness_check              fast
% 7.09/1.49  --demod_use_ground                      true
% 7.09/1.49  --sup_to_prop_solver                    passive
% 7.09/1.49  --sup_prop_simpl_new                    true
% 7.09/1.49  --sup_prop_simpl_given                  true
% 7.09/1.49  --sup_fun_splitting                     false
% 7.09/1.49  --sup_smt_interval                      50000
% 7.09/1.49  
% 7.09/1.49  ------ Superposition Simplification Setup
% 7.09/1.49  
% 7.09/1.49  --sup_indices_passive                   []
% 7.09/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.09/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.09/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.09/1.49  --sup_full_bw                           [BwDemod]
% 7.09/1.49  --sup_immed_triv                        [TrivRules]
% 7.09/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.09/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.09/1.49  --sup_immed_bw_main                     []
% 7.09/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.09/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.09/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.09/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.09/1.49  
% 7.09/1.49  ------ Combination Options
% 7.09/1.49  
% 7.09/1.49  --comb_res_mult                         3
% 7.09/1.49  --comb_sup_mult                         2
% 7.09/1.49  --comb_inst_mult                        10
% 7.09/1.49  
% 7.09/1.49  ------ Debug Options
% 7.09/1.49  
% 7.09/1.49  --dbg_backtrace                         false
% 7.09/1.49  --dbg_dump_prop_clauses                 false
% 7.09/1.49  --dbg_dump_prop_clauses_file            -
% 7.09/1.49  --dbg_out_stat                          false
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  ------ Proving...
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  % SZS status Theorem for theBenchmark.p
% 7.09/1.49  
% 7.09/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.09/1.49  
% 7.09/1.49  fof(f15,conjecture,(
% 7.09/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f16,negated_conjecture,(
% 7.09/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.09/1.49    inference(negated_conjecture,[],[f15])).
% 7.09/1.49  
% 7.09/1.49  fof(f35,plain,(
% 7.09/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.09/1.49    inference(ennf_transformation,[],[f16])).
% 7.09/1.49  
% 7.09/1.49  fof(f36,plain,(
% 7.09/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.09/1.49    inference(flattening,[],[f35])).
% 7.09/1.49  
% 7.09/1.49  fof(f48,plain,(
% 7.09/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.09/1.49    introduced(choice_axiom,[])).
% 7.09/1.49  
% 7.09/1.49  fof(f47,plain,(
% 7.09/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.09/1.49    introduced(choice_axiom,[])).
% 7.09/1.49  
% 7.09/1.49  fof(f46,plain,(
% 7.09/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.09/1.49    introduced(choice_axiom,[])).
% 7.09/1.49  
% 7.09/1.49  fof(f45,plain,(
% 7.09/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.09/1.49    introduced(choice_axiom,[])).
% 7.09/1.49  
% 7.09/1.49  fof(f44,plain,(
% 7.09/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.09/1.49    introduced(choice_axiom,[])).
% 7.09/1.49  
% 7.09/1.49  fof(f43,plain,(
% 7.09/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.09/1.49    introduced(choice_axiom,[])).
% 7.09/1.49  
% 7.09/1.49  fof(f49,plain,(
% 7.09/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.09/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f48,f47,f46,f45,f44,f43])).
% 7.09/1.49  
% 7.09/1.49  fof(f85,plain,(
% 7.09/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f12,axiom,(
% 7.09/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f29,plain,(
% 7.09/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.09/1.49    inference(ennf_transformation,[],[f12])).
% 7.09/1.49  
% 7.09/1.49  fof(f30,plain,(
% 7.09/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.09/1.49    inference(flattening,[],[f29])).
% 7.09/1.49  
% 7.09/1.49  fof(f66,plain,(
% 7.09/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f30])).
% 7.09/1.49  
% 7.09/1.49  fof(f83,plain,(
% 7.09/1.49    v1_funct_1(sK5)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f78,plain,(
% 7.09/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f3,axiom,(
% 7.09/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f18,plain,(
% 7.09/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.09/1.49    inference(ennf_transformation,[],[f3])).
% 7.09/1.49  
% 7.09/1.49  fof(f53,plain,(
% 7.09/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.09/1.49    inference(cnf_transformation,[],[f18])).
% 7.09/1.49  
% 7.09/1.49  fof(f82,plain,(
% 7.09/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f80,plain,(
% 7.09/1.49    v1_funct_1(sK4)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f13,axiom,(
% 7.09/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f31,plain,(
% 7.09/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.49    inference(ennf_transformation,[],[f13])).
% 7.09/1.49  
% 7.09/1.49  fof(f32,plain,(
% 7.09/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.49    inference(flattening,[],[f31])).
% 7.09/1.49  
% 7.09/1.49  fof(f41,plain,(
% 7.09/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.49    inference(nnf_transformation,[],[f32])).
% 7.09/1.49  
% 7.09/1.49  fof(f42,plain,(
% 7.09/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.09/1.49    inference(flattening,[],[f41])).
% 7.09/1.49  
% 7.09/1.49  fof(f68,plain,(
% 7.09/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f42])).
% 7.09/1.49  
% 7.09/1.49  fof(f90,plain,(
% 7.09/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(equality_resolution,[],[f68])).
% 7.09/1.49  
% 7.09/1.49  fof(f14,axiom,(
% 7.09/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f33,plain,(
% 7.09/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.09/1.49    inference(ennf_transformation,[],[f14])).
% 7.09/1.49  
% 7.09/1.49  fof(f34,plain,(
% 7.09/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.49    inference(flattening,[],[f33])).
% 7.09/1.49  
% 7.09/1.49  fof(f70,plain,(
% 7.09/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f34])).
% 7.09/1.49  
% 7.09/1.49  fof(f71,plain,(
% 7.09/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f34])).
% 7.09/1.49  
% 7.09/1.49  fof(f72,plain,(
% 7.09/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f34])).
% 7.09/1.49  
% 7.09/1.49  fof(f4,axiom,(
% 7.09/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f19,plain,(
% 7.09/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.09/1.49    inference(ennf_transformation,[],[f4])).
% 7.09/1.49  
% 7.09/1.49  fof(f54,plain,(
% 7.09/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f19])).
% 7.09/1.49  
% 7.09/1.49  fof(f74,plain,(
% 7.09/1.49    ~v1_xboole_0(sK1)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f75,plain,(
% 7.09/1.49    ~v1_xboole_0(sK2)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f81,plain,(
% 7.09/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f1,axiom,(
% 7.09/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f37,plain,(
% 7.09/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.09/1.49    inference(nnf_transformation,[],[f1])).
% 7.09/1.49  
% 7.09/1.49  fof(f50,plain,(
% 7.09/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f37])).
% 7.09/1.49  
% 7.09/1.49  fof(f8,axiom,(
% 7.09/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f22,plain,(
% 7.09/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.09/1.49    inference(ennf_transformation,[],[f8])).
% 7.09/1.49  
% 7.09/1.49  fof(f23,plain,(
% 7.09/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.49    inference(flattening,[],[f22])).
% 7.09/1.49  
% 7.09/1.49  fof(f39,plain,(
% 7.09/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.09/1.49    inference(nnf_transformation,[],[f23])).
% 7.09/1.49  
% 7.09/1.49  fof(f59,plain,(
% 7.09/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f39])).
% 7.09/1.49  
% 7.09/1.49  fof(f79,plain,(
% 7.09/1.49    r1_subset_1(sK2,sK3)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f77,plain,(
% 7.09/1.49    ~v1_xboole_0(sK3)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f5,axiom,(
% 7.09/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f20,plain,(
% 7.09/1.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.09/1.49    inference(ennf_transformation,[],[f5])).
% 7.09/1.49  
% 7.09/1.49  fof(f55,plain,(
% 7.09/1.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f20])).
% 7.09/1.49  
% 7.09/1.49  fof(f6,axiom,(
% 7.09/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f56,plain,(
% 7.09/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.09/1.49    inference(cnf_transformation,[],[f6])).
% 7.09/1.49  
% 7.09/1.49  fof(f2,axiom,(
% 7.09/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f52,plain,(
% 7.09/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f2])).
% 7.09/1.49  
% 7.09/1.49  fof(f7,axiom,(
% 7.09/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 7.09/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.09/1.49  
% 7.09/1.49  fof(f21,plain,(
% 7.09/1.49    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.09/1.49    inference(ennf_transformation,[],[f7])).
% 7.09/1.49  
% 7.09/1.49  fof(f38,plain,(
% 7.09/1.49    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.09/1.49    inference(nnf_transformation,[],[f21])).
% 7.09/1.49  
% 7.09/1.49  fof(f58,plain,(
% 7.09/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f38])).
% 7.09/1.49  
% 7.09/1.49  fof(f76,plain,(
% 7.09/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f84,plain,(
% 7.09/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  fof(f67,plain,(
% 7.09/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(cnf_transformation,[],[f42])).
% 7.09/1.49  
% 7.09/1.49  fof(f91,plain,(
% 7.09/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.09/1.49    inference(equality_resolution,[],[f67])).
% 7.09/1.49  
% 7.09/1.49  fof(f86,plain,(
% 7.09/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.09/1.49    inference(cnf_transformation,[],[f49])).
% 7.09/1.49  
% 7.09/1.49  cnf(c_24,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.09/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_854,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_24]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1387,plain,
% 7.09/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_16,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.09/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_860,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.49      | ~ v1_funct_1(X0_53)
% 7.09/1.49      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1382,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_860]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2722,plain,
% 7.09/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1387,c_1382]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_26,negated_conjecture,
% 7.09/1.49      ( v1_funct_1(sK5) ),
% 7.09/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1822,plain,
% 7.09/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.09/1.49      | ~ v1_funct_1(sK5)
% 7.09/1.49      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_860]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1988,plain,
% 7.09/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.09/1.49      | ~ v1_funct_1(sK5)
% 7.09/1.49      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_1822]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3005,plain,
% 7.09/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_2722,c_26,c_24,c_1988]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_31,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.09/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_848,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_31]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1393,plain,
% 7.09/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.09/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.09/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_864,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.09/1.49      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1378,plain,
% 7.09/1.49      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_864]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2233,plain,
% 7.09/1.49      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1393,c_1378]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_27,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.09/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_851,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_27]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1390,plain,
% 7.09/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2723,plain,
% 7.09/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.09/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1390,c_1382]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_29,negated_conjecture,
% 7.09/1.49      ( v1_funct_1(sK4) ),
% 7.09/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1827,plain,
% 7.09/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.09/1.49      | ~ v1_funct_1(sK4)
% 7.09/1.49      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_860]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1993,plain,
% 7.09/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.09/1.49      | ~ v1_funct_1(sK4)
% 7.09/1.49      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_1827]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3121,plain,
% 7.09/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_2723,c_29,c_27,c_1993]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.09/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_22,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_21,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_20,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_207,plain,
% 7.09/1.49      ( ~ v1_funct_1(X3)
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_18,c_22,c_21,c_20]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_208,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_207]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_841,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.09/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.09/1.49      | ~ v1_funct_1(X0_53)
% 7.09/1.49      | ~ v1_funct_1(X3_53)
% 7.09/1.49      | v1_xboole_0(X2_53)
% 7.09/1.49      | v1_xboole_0(X1_53)
% 7.09/1.49      | v1_xboole_0(X4_53)
% 7.09/1.49      | v1_xboole_0(X5_53)
% 7.09/1.49      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_208]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1400,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.09/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_4,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.09/1.49      | ~ v1_xboole_0(X1)
% 7.09/1.49      | v1_xboole_0(X0) ),
% 7.09/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_863,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.09/1.49      | ~ v1_xboole_0(X1_53)
% 7.09/1.49      | v1_xboole_0(X0_53) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1379,plain,
% 7.09/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_863]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1618,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
% 7.09/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top ),
% 7.09/1.49      inference(forward_subsumption_resolution,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_1400,c_1379]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_5830,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.09/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.49      | v1_funct_1(sK4) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.09/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_3121,c_1618]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_35,negated_conjecture,
% 7.09/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_38,plain,
% 7.09/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_34,negated_conjecture,
% 7.09/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.09/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_39,plain,
% 7.09/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_44,plain,
% 7.09/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_28,negated_conjecture,
% 7.09/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_45,plain,
% 7.09/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_46,plain,
% 7.09/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_17626,plain,
% 7.09/1.49      ( v1_funct_1(X1_53) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.49      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.09/1.49      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_5830,c_38,c_39,c_44,c_45,c_46]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_17627,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.09/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_17626]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_17648,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_2233,c_17627]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1,plain,
% 7.09/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.09/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_269,plain,
% 7.09/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.09/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_10,plain,
% 7.09/1.49      ( ~ r1_subset_1(X0,X1)
% 7.09/1.49      | r1_xboole_0(X0,X1)
% 7.09/1.49      | v1_xboole_0(X0)
% 7.09/1.49      | v1_xboole_0(X1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_30,negated_conjecture,
% 7.09/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.09/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_510,plain,
% 7.09/1.49      ( r1_xboole_0(X0,X1)
% 7.09/1.49      | v1_xboole_0(X0)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | sK3 != X1
% 7.09/1.49      | sK2 != X0 ),
% 7.09/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_30]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_511,plain,
% 7.09/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.09/1.49      inference(unflattening,[status(thm)],[c_510]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_32,negated_conjecture,
% 7.09/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.09/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_513,plain,
% 7.09/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_511,c_34,c_32]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_599,plain,
% 7.09/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 7.09/1.49      inference(resolution_lifted,[status(thm)],[c_269,c_513]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_600,plain,
% 7.09/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.09/1.49      inference(unflattening,[status(thm)],[c_599]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_836,plain,
% 7.09/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_600]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_17745,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.09/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_17648,c_836]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_17746,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_17745,c_2233]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_5,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.09/1.49      | ~ v1_relat_1(X1)
% 7.09/1.49      | v1_relat_1(X0) ),
% 7.09/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_862,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.09/1.49      | ~ v1_relat_1(X1_53)
% 7.09/1.49      | v1_relat_1(X0_53) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1380,plain,
% 7.09/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.09/1.49      | v1_relat_1(X1_53) != iProver_top
% 7.09/1.49      | v1_relat_1(X0_53) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_862]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2695,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.09/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1390,c_1380]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1746,plain,
% 7.09/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.49      | v1_relat_1(X0_53)
% 7.09/1.49      | ~ v1_relat_1(k2_zfmisc_1(X1_53,X2_53)) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_862]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1930,plain,
% 7.09/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.09/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
% 7.09/1.49      | v1_relat_1(sK4) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_1746]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1931,plain,
% 7.09/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.09/1.49      | v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 7.09/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_6,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.09/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_861,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1974,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_861]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1975,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_1974]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2998,plain,
% 7.09/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_2695,c_46,c_1931,c_1975]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2,plain,
% 7.09/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.09/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_7,plain,
% 7.09/1.49      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 7.09/1.49      | ~ v1_relat_1(X0)
% 7.09/1.49      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 7.09/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_604,plain,
% 7.09/1.49      ( ~ v1_relat_1(X0)
% 7.09/1.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 7.09/1.49      | k1_relat_1(X0) != X2
% 7.09/1.49      | k1_xboole_0 != X1 ),
% 7.09/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_605,plain,
% 7.09/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.49      inference(unflattening,[status(thm)],[c_604]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_835,plain,
% 7.09/1.49      ( ~ v1_relat_1(X0_53)
% 7.09/1.49      | k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_605]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1404,plain,
% 7.09/1.49      ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
% 7.09/1.49      | v1_relat_1(X0_53) != iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3003,plain,
% 7.09/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_2998,c_1404]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_17747,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_17746,c_836,c_3003]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_33,negated_conjecture,
% 7.09/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.09/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_40,plain,
% 7.09/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_41,plain,
% 7.09/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_42,plain,
% 7.09/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18112,plain,
% 7.09/1.49      ( v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53 ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_17747,c_40,c_41,c_42]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18113,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK3) = X0_53
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_18112]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18123,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_3005,c_18113]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2694,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.09/1.49      | v1_relat_1(sK5) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1387,c_1380]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_49,plain,
% 7.09/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1927,plain,
% 7.09/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.09/1.49      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
% 7.09/1.49      | v1_relat_1(sK5) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_1746]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1928,plain,
% 7.09/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 7.09/1.49      | v1_relat_1(sK5) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_1927]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1971,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_861]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1972,plain,
% 7.09/1.49      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2933,plain,
% 7.09/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_2694,c_49,c_1928,c_1972]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2938,plain,
% 7.09/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_2933,c_1404]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18124,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.49      | k1_xboole_0 != k1_xboole_0
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_18123,c_2938]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18125,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(equality_resolution_simp,[status(thm)],[c_18124]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_858,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.09/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.09/1.49      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 7.09/1.49      | ~ v1_funct_1(X0_53)
% 7.09/1.49      | ~ v1_funct_1(X3_53)
% 7.09/1.49      | v1_xboole_0(X2_53)
% 7.09/1.49      | v1_xboole_0(X1_53)
% 7.09/1.49      | v1_xboole_0(X4_53)
% 7.09/1.49      | v1_xboole_0(X5_53) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_20]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1384,plain,
% 7.09/1.49      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X3_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X5_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1563,plain,
% 7.09/1.49      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X3_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.09/1.49      inference(forward_subsumption_resolution,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_1384,c_1379]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3634,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.09/1.49      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X4_53) != iProver_top
% 7.09/1.49      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 7.09/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X2_53) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1563,c_1382]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_856,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.09/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.09/1.49      | ~ v1_funct_1(X0_53)
% 7.09/1.49      | ~ v1_funct_1(X3_53)
% 7.09/1.49      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 7.09/1.49      | v1_xboole_0(X2_53)
% 7.09/1.49      | v1_xboole_0(X1_53)
% 7.09/1.49      | v1_xboole_0(X4_53)
% 7.09/1.49      | v1_xboole_0(X5_53) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1386,plain,
% 7.09/1.49      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X3_53) != iProver_top
% 7.09/1.49      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.09/1.49      | v1_xboole_0(X5_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1511,plain,
% 7.09/1.49      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X3_53) != iProver_top
% 7.09/1.49      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.09/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.09/1.49      inference(forward_subsumption_resolution,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_1386,c_1379]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9292,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.09/1.49      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X4_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X2_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X3_53) = iProver_top ),
% 7.09/1.49      inference(forward_subsumption_resolution,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_3634,c_1511]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9296,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.09/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1387,c_9292]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_47,plain,
% 7.09/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_25,negated_conjecture,
% 7.09/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.09/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_48,plain,
% 7.09/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9449,plain,
% 7.09/1.49      ( v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.09/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_9296,c_38,c_41,c_47,c_48]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9450,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.09/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_9449]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9463,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.09/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(sK4) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1390,c_9450]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9745,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_9463,c_39,c_44,c_45]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9754,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_1393,c_9745]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9824,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_9754,c_40]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_18126,plain,
% 7.09/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_18125,c_9824]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_19,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.09/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_200,plain,
% 7.09/1.49      ( ~ v1_funct_1(X3)
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_19,c_22,c_21,c_20]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_201,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.09/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.09/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.09/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.09/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.09/1.49      | ~ v1_funct_1(X0)
% 7.09/1.49      | ~ v1_funct_1(X3)
% 7.09/1.49      | v1_xboole_0(X1)
% 7.09/1.49      | v1_xboole_0(X2)
% 7.09/1.49      | v1_xboole_0(X4)
% 7.09/1.49      | v1_xboole_0(X5)
% 7.09/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_200]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_842,plain,
% 7.09/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.09/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.09/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.09/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.09/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.09/1.49      | ~ v1_funct_1(X0_53)
% 7.09/1.49      | ~ v1_funct_1(X3_53)
% 7.09/1.49      | v1_xboole_0(X2_53)
% 7.09/1.49      | v1_xboole_0(X1_53)
% 7.09/1.49      | v1_xboole_0(X4_53)
% 7.09/1.49      | v1_xboole_0(X5_53)
% 7.09/1.49      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_201]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1399,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.09/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_1590,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
% 7.09/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.09/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.09/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.09/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.09/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(X4_53) = iProver_top ),
% 7.09/1.49      inference(forward_subsumption_resolution,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_1399,c_1379]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_5009,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.09/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.49      | v1_funct_1(sK4) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.09/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.09/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_3121,c_1590]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_13991,plain,
% 7.09/1.49      ( v1_funct_1(X1_53) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.49      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.09/1.49      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_5009,c_38,c_39,c_44,c_45,c_46]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_13992,plain,
% 7.09/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.09/1.49      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),sK2) = sK4
% 7.09/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.09/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_13991]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14013,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_2233,c_13992]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14110,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.09/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_53,k1_xboole_0)
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_14013,c_836]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14111,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_14110,c_2233]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14112,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_14111,c_836,c_3003]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14436,plain,
% 7.09/1.49      ( v1_funct_1(X0_53) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4 ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_14112,c_40,c_41,c_42]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14437,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_53),sK2) = sK4
% 7.09/1.49      | k2_partfun1(sK3,sK1,X0_53,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | v1_funct_2(X0_53,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(X0_53) != iProver_top ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_14436]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14447,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(superposition,[status(thm)],[c_3005,c_14437]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14448,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.49      | k1_xboole_0 != k1_xboole_0
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_14447,c_2938]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14449,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(equality_resolution_simp,[status(thm)],[c_14448]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_14450,plain,
% 7.09/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.09/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.09/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.09/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_14449,c_9824]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_23,negated_conjecture,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.09/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_855,negated_conjecture,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.09/1.49      inference(subtyping,[status(esa)],[c_23]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2620,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_2233,c_855]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2621,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.09/1.49      inference(light_normalisation,[status(thm)],[c_2620,c_836]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3269,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_2621,c_3005,c_3121]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3274,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_2938,c_3269]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_2812,plain,
% 7.09/1.49      ( ~ v1_relat_1(sK4) | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.09/1.49      inference(instantiation,[status(thm)],[c_835]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3411,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.09/1.49      inference(global_propositional_subsumption,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_3274,c_27,c_1930,c_1974,c_2812]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_3412,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.09/1.49      inference(renaming,[status(thm)],[c_3411]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9828,plain,
% 7.09/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.09/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_9824,c_3412]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(c_9829,plain,
% 7.09/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.09/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.09/1.49      inference(demodulation,[status(thm)],[c_9828,c_9824]) ).
% 7.09/1.49  
% 7.09/1.49  cnf(contradiction,plain,
% 7.09/1.49      ( $false ),
% 7.09/1.49      inference(minisat,
% 7.09/1.49                [status(thm)],
% 7.09/1.49                [c_18126,c_14450,c_9829,c_49,c_48,c_47]) ).
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.09/1.49  
% 7.09/1.49  ------                               Statistics
% 7.09/1.49  
% 7.09/1.49  ------ General
% 7.09/1.49  
% 7.09/1.49  abstr_ref_over_cycles:                  0
% 7.09/1.49  abstr_ref_under_cycles:                 0
% 7.09/1.49  gc_basic_clause_elim:                   0
% 7.09/1.49  forced_gc_time:                         0
% 7.09/1.49  parsing_time:                           0.012
% 7.09/1.49  unif_index_cands_time:                  0.
% 7.09/1.49  unif_index_add_time:                    0.
% 7.09/1.49  orderings_time:                         0.
% 7.09/1.49  out_proof_time:                         0.022
% 7.09/1.49  total_time:                             0.953
% 7.09/1.49  num_of_symbols:                         58
% 7.09/1.49  num_of_terms:                           36108
% 7.09/1.49  
% 7.09/1.49  ------ Preprocessing
% 7.09/1.49  
% 7.09/1.49  num_of_splits:                          0
% 7.09/1.49  num_of_split_atoms:                     0
% 7.09/1.49  num_of_reused_defs:                     0
% 7.09/1.49  num_eq_ax_congr_red:                    11
% 7.09/1.49  num_of_sem_filtered_clauses:            1
% 7.09/1.49  num_of_subtypes:                        2
% 7.09/1.49  monotx_restored_types:                  0
% 7.09/1.49  sat_num_of_epr_types:                   0
% 7.09/1.49  sat_num_of_non_cyclic_types:            0
% 7.09/1.49  sat_guarded_non_collapsed_types:        1
% 7.09/1.49  num_pure_diseq_elim:                    0
% 7.09/1.49  simp_replaced_by:                       0
% 7.09/1.49  res_preprocessed:                       162
% 7.09/1.49  prep_upred:                             0
% 7.09/1.49  prep_unflattend:                        17
% 7.09/1.49  smt_new_axioms:                         0
% 7.09/1.49  pred_elim_cands:                        5
% 7.09/1.49  pred_elim:                              4
% 7.09/1.49  pred_elim_cl:                           5
% 7.09/1.49  pred_elim_cycles:                       7
% 7.09/1.49  merged_defs:                            2
% 7.09/1.49  merged_defs_ncl:                        0
% 7.09/1.49  bin_hyper_res:                          2
% 7.09/1.49  prep_cycles:                            4
% 7.09/1.49  pred_elim_time:                         0.005
% 7.09/1.49  splitting_time:                         0.
% 7.09/1.49  sem_filter_time:                        0.
% 7.09/1.49  monotx_time:                            0.
% 7.09/1.49  subtype_inf_time:                       0.001
% 7.09/1.49  
% 7.09/1.49  ------ Problem properties
% 7.09/1.49  
% 7.09/1.49  clauses:                                31
% 7.09/1.49  conjectures:                            13
% 7.09/1.49  epr:                                    8
% 7.09/1.49  horn:                                   24
% 7.09/1.49  ground:                                 14
% 7.09/1.49  unary:                                  15
% 7.09/1.49  binary:                                 2
% 7.09/1.49  lits:                                   130
% 7.09/1.49  lits_eq:                                21
% 7.09/1.49  fd_pure:                                0
% 7.09/1.49  fd_pseudo:                              0
% 7.09/1.49  fd_cond:                                0
% 7.09/1.49  fd_pseudo_cond:                         1
% 7.09/1.49  ac_symbols:                             0
% 7.09/1.49  
% 7.09/1.49  ------ Propositional Solver
% 7.09/1.49  
% 7.09/1.49  prop_solver_calls:                      29
% 7.09/1.49  prop_fast_solver_calls:                 2651
% 7.09/1.49  smt_solver_calls:                       0
% 7.09/1.49  smt_fast_solver_calls:                  0
% 7.09/1.49  prop_num_of_clauses:                    7710
% 7.09/1.49  prop_preprocess_simplified:             16039
% 7.09/1.49  prop_fo_subsumed:                       219
% 7.09/1.49  prop_solver_time:                       0.
% 7.09/1.49  smt_solver_time:                        0.
% 7.09/1.49  smt_fast_solver_time:                   0.
% 7.09/1.49  prop_fast_solver_time:                  0.
% 7.09/1.49  prop_unsat_core_time:                   0.001
% 7.09/1.49  
% 7.09/1.49  ------ QBF
% 7.09/1.49  
% 7.09/1.49  qbf_q_res:                              0
% 7.09/1.49  qbf_num_tautologies:                    0
% 7.09/1.49  qbf_prep_cycles:                        0
% 7.09/1.49  
% 7.09/1.49  ------ BMC1
% 7.09/1.49  
% 7.09/1.49  bmc1_current_bound:                     -1
% 7.09/1.49  bmc1_last_solved_bound:                 -1
% 7.09/1.49  bmc1_unsat_core_size:                   -1
% 7.09/1.49  bmc1_unsat_core_parents_size:           -1
% 7.09/1.49  bmc1_merge_next_fun:                    0
% 7.09/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.09/1.49  
% 7.09/1.49  ------ Instantiation
% 7.09/1.49  
% 7.09/1.49  inst_num_of_clauses:                    1799
% 7.09/1.49  inst_num_in_passive:                    966
% 7.09/1.49  inst_num_in_active:                     750
% 7.09/1.49  inst_num_in_unprocessed:                83
% 7.09/1.49  inst_num_of_loops:                      770
% 7.09/1.49  inst_num_of_learning_restarts:          0
% 7.09/1.49  inst_num_moves_active_passive:          15
% 7.09/1.49  inst_lit_activity:                      0
% 7.09/1.49  inst_lit_activity_moves:                0
% 7.09/1.49  inst_num_tautologies:                   0
% 7.09/1.49  inst_num_prop_implied:                  0
% 7.09/1.49  inst_num_existing_simplified:           0
% 7.09/1.49  inst_num_eq_res_simplified:             0
% 7.09/1.49  inst_num_child_elim:                    0
% 7.09/1.49  inst_num_of_dismatching_blockings:      90
% 7.09/1.49  inst_num_of_non_proper_insts:           1270
% 7.09/1.49  inst_num_of_duplicates:                 0
% 7.09/1.49  inst_inst_num_from_inst_to_res:         0
% 7.09/1.49  inst_dismatching_checking_time:         0.
% 7.09/1.49  
% 7.09/1.49  ------ Resolution
% 7.09/1.49  
% 7.09/1.49  res_num_of_clauses:                     0
% 7.09/1.49  res_num_in_passive:                     0
% 7.09/1.49  res_num_in_active:                      0
% 7.09/1.49  res_num_of_loops:                       166
% 7.09/1.49  res_forward_subset_subsumed:            52
% 7.09/1.49  res_backward_subset_subsumed:           2
% 7.09/1.49  res_forward_subsumed:                   0
% 7.09/1.49  res_backward_subsumed:                  0
% 7.09/1.49  res_forward_subsumption_resolution:     0
% 7.09/1.49  res_backward_subsumption_resolution:    0
% 7.09/1.49  res_clause_to_clause_subsumption:       1473
% 7.09/1.49  res_orphan_elimination:                 0
% 7.09/1.49  res_tautology_del:                      51
% 7.09/1.49  res_num_eq_res_simplified:              0
% 7.09/1.49  res_num_sel_changes:                    0
% 7.09/1.49  res_moves_from_active_to_pass:          0
% 7.09/1.49  
% 7.09/1.49  ------ Superposition
% 7.09/1.49  
% 7.09/1.49  sup_time_total:                         0.
% 7.09/1.49  sup_time_generating:                    0.
% 7.09/1.49  sup_time_sim_full:                      0.
% 7.09/1.49  sup_time_sim_immed:                     0.
% 7.09/1.49  
% 7.09/1.49  sup_num_of_clauses:                     270
% 7.09/1.49  sup_num_in_active:                      149
% 7.09/1.49  sup_num_in_passive:                     121
% 7.09/1.49  sup_num_of_loops:                       153
% 7.09/1.49  sup_fw_superposition:                   239
% 7.09/1.49  sup_bw_superposition:                   69
% 7.09/1.49  sup_immediate_simplified:               137
% 7.09/1.49  sup_given_eliminated:                   0
% 7.09/1.49  comparisons_done:                       0
% 7.09/1.49  comparisons_avoided:                    0
% 7.09/1.49  
% 7.09/1.49  ------ Simplifications
% 7.09/1.49  
% 7.09/1.49  
% 7.09/1.49  sim_fw_subset_subsumed:                 7
% 7.09/1.49  sim_bw_subset_subsumed:                 0
% 7.09/1.49  sim_fw_subsumed:                        15
% 7.09/1.49  sim_bw_subsumed:                        8
% 7.09/1.49  sim_fw_subsumption_res:                 13
% 7.09/1.49  sim_bw_subsumption_res:                 0
% 7.09/1.49  sim_tautology_del:                      0
% 7.09/1.49  sim_eq_tautology_del:                   11
% 7.09/1.49  sim_eq_res_simp:                        4
% 7.09/1.49  sim_fw_demodulated:                     77
% 7.09/1.49  sim_bw_demodulated:                     5
% 7.09/1.49  sim_light_normalised:                   46
% 7.09/1.49  sim_joinable_taut:                      0
% 7.09/1.49  sim_joinable_simp:                      0
% 7.09/1.49  sim_ac_normalised:                      0
% 7.09/1.49  sim_smt_subsumption:                    0
% 7.09/1.49  
%------------------------------------------------------------------------------
