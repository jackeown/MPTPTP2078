%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:27 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 597 expanded)
%              Number of clauses        :   91 ( 135 expanded)
%              Number of leaves         :   19 ( 240 expanded)
%              Depth                    :   22
%              Number of atoms          :  968 (8071 expanded)
%              Number of equality atoms :  221 (1792 expanded)
%              Maximal formula depth    :   25 (   7 average)
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

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ~ v1_xboole_0(sK3) ),
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

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
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

fof(f80,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
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

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1804,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1810,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2894,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1810])).

cnf(c_2,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1815,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2555,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1815])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1811,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3117,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_1811])).

cnf(c_4362,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2894,c_3117])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_534,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_535,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_537,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_34,c_32])).

cnf(c_1790,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1816,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2724,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1790,c_1816])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1798,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1813,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3009,plain,
    ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1798,c_1813])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1801,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1809,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3123,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1801,c_1809])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2022,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2240,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_5210,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3123,c_29,c_27,c_2240])).

cnf(c_3122,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1809])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2017,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2235,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2017])).

cnf(c_5038,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3122,c_26,c_24,c_2235])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_5041,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_5038,c_23])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1036,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1976,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_2161,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_1035,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2162,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_2377,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_3454,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2377])).

cnf(c_3455,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2235])).

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

cnf(c_2097,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
    | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X3) = sK4 ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_2349,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK4,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
    | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X2) = sK4 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_2707,plain,
    ( ~ v1_funct_2(sK5,X0,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
    | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_2349])).

cnf(c_3084,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2707])).

cnf(c_4062,plain,
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
    inference(instantiation,[status(thm)],[c_3084])).

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

cnf(c_2107,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
    | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X1) = X0 ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_2367,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK4,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
    | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_2107])).

cnf(c_2819,plain,
    ( ~ v1_funct_2(sK5,X0,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
    | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_2367])).

cnf(c_3105,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2819])).

cnf(c_4142,plain,
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
    inference(instantiation,[status(thm)],[c_3105])).

cnf(c_5058,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5041,c_36,c_35,c_34,c_33,c_32,c_31,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_2161,c_2162,c_3454,c_3455,c_4062,c_4142])).

cnf(c_5213,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_5210,c_5058])).

cnf(c_7620,plain,
    ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3009,c_5213])).

cnf(c_8317,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3009,c_7620])).

cnf(c_8318,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2724,c_8317])).

cnf(c_8376,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2724,c_8318])).

cnf(c_8377,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4362,c_8376])).

cnf(c_3447,plain,
    ( k4_xboole_0(k1_xboole_0,k1_relat_1(sK4)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1938,plain,
    ( r1_xboole_0(k1_xboole_0,X0)
    | k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2448,plain,
    ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | k4_xboole_0(k1_xboole_0,k1_relat_1(sK4)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_2117,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2447,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_1912,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8377,c_3447,c_2448,c_2447,c_1912,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:18:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.87/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.87/0.98  
% 3.87/0.98  ------  iProver source info
% 3.87/0.98  
% 3.87/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.87/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.87/0.98  git: non_committed_changes: false
% 3.87/0.98  git: last_make_outside_of_git: false
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  ------ Parsing...
% 3.87/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.87/0.98  
% 3.87/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.87/0.98  ------ Proving...
% 3.87/0.98  ------ Problem Properties 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  clauses                                 31
% 3.87/0.98  conjectures                             13
% 3.87/0.98  EPR                                     9
% 3.87/0.98  Horn                                    24
% 3.87/0.98  unary                                   14
% 3.87/0.98  binary                                  6
% 3.87/0.98  lits                                    127
% 3.87/0.98  lits eq                                 18
% 3.87/0.98  fd_pure                                 0
% 3.87/0.98  fd_pseudo                               0
% 3.87/0.98  fd_cond                                 0
% 3.87/0.98  fd_pseudo_cond                          1
% 3.87/0.98  AC symbols                              0
% 3.87/0.98  
% 3.87/0.98  ------ Input Options Time Limit: Unbounded
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ 
% 3.87/0.98  Current options:
% 3.87/0.98  ------ 
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  ------ Proving...
% 3.87/0.98  
% 3.87/0.98  
% 3.87/0.98  % SZS status Theorem for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.87/0.98  
% 3.87/0.98  fof(f15,conjecture,(
% 3.87/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f16,negated_conjecture,(
% 3.87/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.87/0.98    inference(negated_conjecture,[],[f15])).
% 3.87/0.98  
% 3.87/0.98  fof(f35,plain,(
% 3.87/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.87/0.98    inference(ennf_transformation,[],[f16])).
% 3.87/0.98  
% 3.87/0.98  fof(f36,plain,(
% 3.87/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.87/0.98    inference(flattening,[],[f35])).
% 3.87/0.98  
% 3.87/0.98  fof(f48,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f47,plain,(
% 3.87/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f46,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f45,plain,(
% 3.87/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f44,plain,(
% 3.87/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f43,plain,(
% 3.87/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.87/0.98    introduced(choice_axiom,[])).
% 3.87/0.98  
% 3.87/0.98  fof(f49,plain,(
% 3.87/0.98    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.87/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f36,f48,f47,f46,f45,f44,f43])).
% 3.87/0.98  
% 3.87/0.98  fof(f85,plain,(
% 3.87/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f8,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f23,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.87/0.98    inference(ennf_transformation,[],[f8])).
% 3.87/0.98  
% 3.87/0.98  fof(f60,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f23])).
% 3.87/0.98  
% 3.87/0.98  fof(f2,axiom,(
% 3.87/0.98    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f52,plain,(
% 3.87/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f2])).
% 3.87/0.98  
% 3.87/0.98  fof(f3,axiom,(
% 3.87/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f38,plain,(
% 3.87/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.87/0.98    inference(nnf_transformation,[],[f3])).
% 3.87/0.98  
% 3.87/0.98  fof(f54,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.87/0.98    inference(cnf_transformation,[],[f38])).
% 3.87/0.98  
% 3.87/0.98  fof(f6,axiom,(
% 3.87/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f20,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.87/0.98    inference(ennf_transformation,[],[f6])).
% 3.87/0.98  
% 3.87/0.98  fof(f57,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f20])).
% 3.87/0.98  
% 3.87/0.98  fof(f7,axiom,(
% 3.87/0.98    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f21,plain,(
% 3.87/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.87/0.98    inference(ennf_transformation,[],[f7])).
% 3.87/0.98  
% 3.87/0.98  fof(f22,plain,(
% 3.87/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.87/0.98    inference(flattening,[],[f21])).
% 3.87/0.98  
% 3.87/0.98  fof(f39,plain,(
% 3.87/0.98    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.87/0.98    inference(nnf_transformation,[],[f22])).
% 3.87/0.98  
% 3.87/0.98  fof(f58,plain,(
% 3.87/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f39])).
% 3.87/0.98  
% 3.87/0.98  fof(f79,plain,(
% 3.87/0.98    r1_subset_1(sK2,sK3)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f75,plain,(
% 3.87/0.98    ~v1_xboole_0(sK2)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f77,plain,(
% 3.87/0.98    ~v1_xboole_0(sK3)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f1,axiom,(
% 3.87/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f37,plain,(
% 3.87/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.87/0.98    inference(nnf_transformation,[],[f1])).
% 3.87/0.98  
% 3.87/0.98  fof(f50,plain,(
% 3.87/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f37])).
% 3.87/0.98  
% 3.87/0.98  fof(f78,plain,(
% 3.87/0.98    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f4,axiom,(
% 3.87/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f18,plain,(
% 3.87/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.87/0.98    inference(ennf_transformation,[],[f4])).
% 3.87/0.98  
% 3.87/0.98  fof(f55,plain,(
% 3.87/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.87/0.98    inference(cnf_transformation,[],[f18])).
% 3.87/0.98  
% 3.87/0.98  fof(f82,plain,(
% 3.87/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f12,axiom,(
% 3.87/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f29,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.87/0.98    inference(ennf_transformation,[],[f12])).
% 3.87/0.98  
% 3.87/0.98  fof(f30,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.87/0.98    inference(flattening,[],[f29])).
% 3.87/0.98  
% 3.87/0.98  fof(f66,plain,(
% 3.87/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f30])).
% 3.87/0.98  
% 3.87/0.98  fof(f80,plain,(
% 3.87/0.98    v1_funct_1(sK4)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f83,plain,(
% 3.87/0.98    v1_funct_1(sK5)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f86,plain,(
% 3.87/0.98    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f73,plain,(
% 3.87/0.98    ~v1_xboole_0(sK0)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f74,plain,(
% 3.87/0.98    ~v1_xboole_0(sK1)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f76,plain,(
% 3.87/0.98    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f81,plain,(
% 3.87/0.98    v1_funct_2(sK4,sK2,sK1)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f84,plain,(
% 3.87/0.98    v1_funct_2(sK5,sK3,sK1)),
% 3.87/0.98    inference(cnf_transformation,[],[f49])).
% 3.87/0.98  
% 3.87/0.98  fof(f13,axiom,(
% 3.87/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f31,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.87/0.98    inference(ennf_transformation,[],[f13])).
% 3.87/0.98  
% 3.87/0.98  fof(f32,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.87/0.98    inference(flattening,[],[f31])).
% 3.87/0.98  
% 3.87/0.98  fof(f41,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.87/0.98    inference(nnf_transformation,[],[f32])).
% 3.87/0.98  
% 3.87/0.98  fof(f42,plain,(
% 3.87/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.87/0.98    inference(flattening,[],[f41])).
% 3.87/0.98  
% 3.87/0.98  fof(f67,plain,(
% 3.87/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f42])).
% 3.87/0.98  
% 3.87/0.98  fof(f91,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(equality_resolution,[],[f67])).
% 3.87/0.98  
% 3.87/0.98  fof(f14,axiom,(
% 3.87/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.87/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.87/0.98  
% 3.87/0.98  fof(f33,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.87/0.98    inference(ennf_transformation,[],[f14])).
% 3.87/0.98  
% 3.87/0.98  fof(f34,plain,(
% 3.87/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.87/0.98    inference(flattening,[],[f33])).
% 3.87/0.98  
% 3.87/0.98  fof(f70,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f34])).
% 3.87/0.98  
% 3.87/0.98  fof(f71,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f34])).
% 3.87/0.98  
% 3.87/0.98  fof(f72,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f34])).
% 3.87/0.98  
% 3.87/0.98  fof(f68,plain,(
% 3.87/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(cnf_transformation,[],[f42])).
% 3.87/0.98  
% 3.87/0.98  fof(f90,plain,(
% 3.87/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.87/0.98    inference(equality_resolution,[],[f68])).
% 3.87/0.98  
% 3.87/0.98  cnf(c_24,negated_conjecture,
% 3.87/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.87/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1804,plain,
% 3.87/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_10,plain,
% 3.87/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.98      | v1_relat_1(X0) ),
% 3.87/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1810,plain,
% 3.87/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2894,plain,
% 3.87/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_1804,c_1810]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2,plain,
% 3.87/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3,plain,
% 3.87/0.98      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1815,plain,
% 3.87/0.98      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_2555,plain,
% 3.87/0.98      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_2,c_1815]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_7,plain,
% 3.87/0.98      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.87/0.98      | ~ v1_relat_1(X1)
% 3.87/0.98      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.87/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_1811,plain,
% 3.87/0.98      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.87/0.98      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_3117,plain,
% 3.87/0.98      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.87/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_2555,c_1811]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_4362,plain,
% 3.87/0.98      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.98      inference(superposition,[status(thm)],[c_2894,c_3117]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_9,plain,
% 3.87/0.98      ( ~ r1_subset_1(X0,X1)
% 3.87/0.98      | r1_xboole_0(X0,X1)
% 3.87/0.98      | v1_xboole_0(X0)
% 3.87/0.98      | v1_xboole_0(X1) ),
% 3.87/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_30,negated_conjecture,
% 3.87/0.98      ( r1_subset_1(sK2,sK3) ),
% 3.87/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_534,plain,
% 3.87/0.98      ( r1_xboole_0(X0,X1)
% 3.87/0.98      | v1_xboole_0(X0)
% 3.87/0.98      | v1_xboole_0(X1)
% 3.87/0.98      | sK3 != X1
% 3.87/0.98      | sK2 != X0 ),
% 3.87/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_535,plain,
% 3.87/0.98      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 3.87/0.98      inference(unflattening,[status(thm)],[c_534]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_34,negated_conjecture,
% 3.87/0.98      ( ~ v1_xboole_0(sK2) ),
% 3.87/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_32,negated_conjecture,
% 3.87/0.98      ( ~ v1_xboole_0(sK3) ),
% 3.87/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.87/0.98  
% 3.87/0.98  cnf(c_537,plain,
% 3.87/0.98      ( r1_xboole_0(sK2,sK3) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_535,c_34,c_32]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1790,plain,
% 3.87/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1,plain,
% 3.87/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1816,plain,
% 3.87/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 3.87/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2724,plain,
% 3.87/0.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1790,c_1816]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_31,negated_conjecture,
% 3.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1798,plain,
% 3.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.87/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1813,plain,
% 3.87/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.87/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3009,plain,
% 3.87/0.99      ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1798,c_1813]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_27,negated_conjecture,
% 3.87/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.87/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1801,plain,
% 3.87/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_16,plain,
% 3.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.87/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1809,plain,
% 3.87/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.87/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.87/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.87/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3123,plain,
% 3.87/0.99      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 3.87/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1801,c_1809]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_29,negated_conjecture,
% 3.87/0.99      ( v1_funct_1(sK4) ),
% 3.87/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2022,plain,
% 3.87/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2240,plain,
% 3.87/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2022]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5210,plain,
% 3.87/0.99      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3123,c_29,c_27,c_2240]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3122,plain,
% 3.87/0.99      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 3.87/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_1804,c_1809]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_26,negated_conjecture,
% 3.87/0.99      ( v1_funct_1(sK5) ),
% 3.87/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2017,plain,
% 3.87/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2235,plain,
% 3.87/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2017]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5038,plain,
% 3.87/0.99      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_3122,c_26,c_24,c_2235]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_23,negated_conjecture,
% 3.87/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.87/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5041,plain,
% 3.87/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.87/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_5038,c_23]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_36,negated_conjecture,
% 3.87/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.87/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_35,negated_conjecture,
% 3.87/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_33,negated_conjecture,
% 3.87/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 3.87/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_28,negated_conjecture,
% 3.87/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_25,negated_conjecture,
% 3.87/0.99      ( v1_funct_2(sK5,sK3,sK1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1036,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1976,plain,
% 3.87/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1036]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2161,plain,
% 3.87/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1035,plain,( X0 = X0 ),theory(equality) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2162,plain,
% 3.87/0.99      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1035]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2377,plain,
% 3.87/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1036]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3454,plain,
% 3.87/0.99      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
% 3.87/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2377]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3455,plain,
% 3.87/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2235]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_19,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.87/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_22,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_21,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_20,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1) ),
% 3.87/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_198,plain,
% 3.87/0.99      ( ~ v1_funct_1(X3)
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_19,c_22,c_21,c_20]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_199,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_198]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2097,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(sK4,X3,X2)
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X3)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X3) = sK4 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_199]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2349,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 3.87/0.99      | ~ v1_funct_2(sK4,X2,X1)
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 3.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X3)
% 3.87/0.99      | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X2) = sK4 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2097]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2707,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,X0,sK1)
% 3.87/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(sK1)
% 3.87/0.99      | v1_xboole_0(sK2)
% 3.87/0.99      | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),sK2) = sK4 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2349]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3084,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.87/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(sK1)
% 3.87/0.99      | v1_xboole_0(sK3)
% 3.87/0.99      | v1_xboole_0(sK2)
% 3.87/0.99      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2707]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4062,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.87/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 3.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(sK1)
% 3.87/0.99      | v1_xboole_0(sK3)
% 3.87/0.99      | v1_xboole_0(sK2)
% 3.87/0.99      | v1_xboole_0(sK0)
% 3.87/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_3084]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_18,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.87/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_205,plain,
% 3.87/0.99      ( ~ v1_funct_1(X3)
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_18,c_22,c_21,c_20]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_206,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.87/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(X3)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | v1_xboole_0(X5)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.87/0.99      inference(renaming,[status(thm)],[c_205]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2107,plain,
% 3.87/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.87/0.99      | ~ v1_funct_2(sK4,X3,X2)
% 3.87/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 3.87/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.87/0.99      | ~ v1_funct_1(X0)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X3)
% 3.87/0.99      | v1_xboole_0(X4)
% 3.87/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X1) = X0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_206]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2367,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 3.87/0.99      | ~ v1_funct_2(sK4,X2,X1)
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 3.87/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(X2)
% 3.87/0.99      | v1_xboole_0(X3)
% 3.87/0.99      | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X0) = sK5 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2107]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2819,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,X0,sK1)
% 3.87/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.87/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(X1)
% 3.87/0.99      | v1_xboole_0(sK1)
% 3.87/0.99      | v1_xboole_0(sK2)
% 3.87/0.99      | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
% 3.87/0.99      | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),X0) = sK5 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2367]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3105,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.87/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 3.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(X0)
% 3.87/0.99      | v1_xboole_0(sK1)
% 3.87/0.99      | v1_xboole_0(sK3)
% 3.87/0.99      | v1_xboole_0(sK2)
% 3.87/0.99      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2819]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_4142,plain,
% 3.87/0.99      ( ~ v1_funct_2(sK5,sK3,sK1)
% 3.87/0.99      | ~ v1_funct_2(sK4,sK2,sK1)
% 3.87/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 3.87/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 3.87/0.99      | ~ v1_funct_1(sK5)
% 3.87/0.99      | ~ v1_funct_1(sK4)
% 3.87/0.99      | v1_xboole_0(sK1)
% 3.87/0.99      | v1_xboole_0(sK3)
% 3.87/0.99      | v1_xboole_0(sK2)
% 3.87/0.99      | v1_xboole_0(sK0)
% 3.87/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.87/0.99      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_3105]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5058,plain,
% 3.87/0.99      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(global_propositional_subsumption,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_5041,c_36,c_35,c_34,c_33,c_32,c_31,c_29,c_28,c_27,
% 3.87/0.99                 c_26,c_25,c_24,c_23,c_2161,c_2162,c_3454,c_3455,c_4062,
% 3.87/0.99                 c_4142]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_5213,plain,
% 3.87/0.99      ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_5210,c_5058]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_7620,plain,
% 3.87/0.99      ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_3009,c_5213]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8317,plain,
% 3.87/0.99      ( k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_3009,c_7620]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8318,plain,
% 3.87/0.99      ( k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_2724,c_8317]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8376,plain,
% 3.87/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_2724,c_8318]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_8377,plain,
% 3.87/0.99      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 3.87/0.99      inference(superposition,[status(thm)],[c_4362,c_8376]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_3447,plain,
% 3.87/0.99      ( k4_xboole_0(k1_xboole_0,k1_relat_1(sK4)) = k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1938,plain,
% 3.87/0.99      ( r1_xboole_0(k1_xboole_0,X0)
% 3.87/0.99      | k4_xboole_0(k1_xboole_0,X0) != k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2448,plain,
% 3.87/0.99      ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
% 3.87/0.99      | k4_xboole_0(k1_xboole_0,k1_relat_1(sK4)) != k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_1938]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2117,plain,
% 3.87/0.99      ( ~ r1_xboole_0(X0,k1_relat_1(sK4))
% 3.87/0.99      | ~ v1_relat_1(sK4)
% 3.87/0.99      | k7_relat_1(sK4,X0) = k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_2447,plain,
% 3.87/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
% 3.87/0.99      | ~ v1_relat_1(sK4)
% 3.87/0.99      | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_2117]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(c_1912,plain,
% 3.87/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.87/0.99      | v1_relat_1(sK4) ),
% 3.87/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.87/0.99  
% 3.87/0.99  cnf(contradiction,plain,
% 3.87/0.99      ( $false ),
% 3.87/0.99      inference(minisat,
% 3.87/0.99                [status(thm)],
% 3.87/0.99                [c_8377,c_3447,c_2448,c_2447,c_1912,c_27]) ).
% 3.87/0.99  
% 3.87/0.99  
% 3.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.87/0.99  
% 3.87/0.99  ------                               Statistics
% 3.87/0.99  
% 3.87/0.99  ------ Selected
% 3.87/0.99  
% 3.87/0.99  total_time:                             0.342
% 3.87/0.99  
%------------------------------------------------------------------------------
